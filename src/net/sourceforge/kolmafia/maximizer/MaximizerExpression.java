package net.sourceforge.kolmafia.maximizer;

import java.util.ArrayList;
import java.util.EnumMap;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import net.sourceforge.kolmafia.AdventureResult;
import net.sourceforge.kolmafia.FamiliarData;
import net.sourceforge.kolmafia.KoLCharacter;
import net.sourceforge.kolmafia.KoLConstants.MafiaState;
import net.sourceforge.kolmafia.KoLmafia;
import net.sourceforge.kolmafia.Modeable;
import net.sourceforge.kolmafia.Modifiers;
import net.sourceforge.kolmafia.SpecialOutfit;
import net.sourceforge.kolmafia.equipment.Slot;
import net.sourceforge.kolmafia.equipment.SlotSet;
import net.sourceforge.kolmafia.modifiers.BitmapModifier;
import net.sourceforge.kolmafia.modifiers.BooleanModifier;
import net.sourceforge.kolmafia.modifiers.DoubleModifier;
import net.sourceforge.kolmafia.modifiers.Modifier;
import net.sourceforge.kolmafia.modifiers.StringModifier;
import net.sourceforge.kolmafia.objectpool.ItemPool;
import net.sourceforge.kolmafia.persistence.AdventureDatabase;
import net.sourceforge.kolmafia.persistence.FamiliarDatabase;
import net.sourceforge.kolmafia.persistence.ItemFinder;
import net.sourceforge.kolmafia.persistence.ItemFinder.Match;
import net.sourceforge.kolmafia.preferences.Preferences;
import net.sourceforge.kolmafia.request.EquipmentRequest;
import net.sourceforge.kolmafia.session.EquipmentManager;
import net.sourceforge.kolmafia.session.InventoryManager;
import net.sourceforge.kolmafia.utilities.StringUtilities;

class MaximizerExpression {
  static final String TIEBREAKER =
      "1 familiar weight, 1 familiar experience, 1 initiative, 5 exp, 1 item, 1 meat, 0.1 DA 1000 max, 1 DR, 0.5 all res, -10 mana cost, 1.0 mus, 0.5 mys, 1.0 mox, 1.5 mainstat, 1 HP, 1 MP, 1 weapon damage, 1 ranged damage, 1 spell damage, 1 cold damage, 1 hot damage, 1 sleaze damage, 1 spooky damage, 1 stench damage, 1 cold spell damage, 1 hot spell damage, 1 sleaze spell damage, 1 spooky spell damage, 1 stench spell damage, -1 fumble, 1 HP regen max, 3 MP regen max, 1 critical hit percent, 0.1 food drop, 0.1 booze drop, 0.1 hat drop, 0.1 weapon drop, 0.1 offhand drop, 0.1 shirt drop, 0.1 pants drop, 0.1 accessory drop, 1 DB combat damage, 0.1 sixgun damage";
  static final Set<BitmapModifier> OSITY_MODIFIERS =
      EnumSet.of(BitmapModifier.CLOWNINESS, BitmapModifier.RAVEOSITY, BitmapModifier.SURGEONOSITY);

  final Map<Modifier, Double> weight = new HashMap<>();
  final Map<Modifier, Double> min = new HashMap<>();
  final Map<Modifier, Double> max = new HashMap<>();
  double totalMin = Double.NEGATIVE_INFINITY;
  double totalMax = Double.POSITIVE_INFINITY;
  int dump = 0;
  int stinkycheese = 0;
  int beeosity = 2;
  final EnumSet<BooleanModifier> booleanMask = EnumSet.noneOf(BooleanModifier.class);
  final Set<BooleanModifier> booleanValue = EnumSet.noneOf(BooleanModifier.class);
  final List<FamiliarData> familiars = new ArrayList<>();

  // Some modeables are forced based on certain expressions appearing in a maximize call.
  final Map<Modeable, String> forcedModeables = Modeable.getStringMap(modeable -> "");

  /** If slots[i] >= 0 then equipment of type i can be considered for maximization. */
  final EnumMap<Slot, Integer> slots = new EnumMap<>(Slot.class);

  String weaponType = null;
  int hands = 0;
  int melee = 0;
  boolean effective = false;
  boolean requireClub = false;
  boolean requireShield = false;
  boolean requireUtensil = false;
  boolean requireSword = false;
  boolean requireKnife = false;
  boolean requireAccordion = false;
  boolean noTiebreaker = false;
  boolean current = !KoLCharacter.canInteract() || Preferences.getBoolean("maximizerAlwaysCurrent");
  final Set<String> posOutfits = new HashSet<>();
  final Set<String> negOutfits = new HashSet<>();
  final Set<AdventureResult> posEquip = new HashSet<>();
  final Set<AdventureResult> negEquip = new HashSet<>();
  final Map<AdventureResult, ItemBonus> bonuses = new HashMap<>();
  final Map<BooleanModifier, Double> modBonuses = new HashMap<>();
  final List<BonusFunction> bonusFunc = new ArrayList<>();

  record BonusFunction(Function<AdventureResult, Double> bonusFunction, Double weight) {}

  record ItemBonus(double base, Map<String, Double> modes) {}

  private record Canonicalization(Pattern pattern, String canonical) {}

  private record Directive(String name, String rawArgument) {
    private static final Set<String> PARAMETERIZED_NAMES =
        Set.of("type", "equip", "bonus", "modbonus", "letter", "outfit", "switch");
    private static final Set<String> REQUIRED_ARGUMENT_NAMES =
        Set.of("type", "equip", "bonus", "modbonus", "switch");

    private static Directive parse(String text) {
      if (text.startsWith("\"") && text.endsWith("\"")) {
        text = text.substring(1, text.length() - 1).trim();
      }
      text = DIRECTIVE_ALIASES.getOrDefault(text, text);

      String[] parts = text.split(" ", 2);
      if (parts.length == 1 || !PARAMETERIZED_NAMES.contains(parts[0])) {
        return new Directive(text, "");
      }

      return new Directive(parts[0], parts[1]);
    }

    private boolean is(String name) {
      return this.name.equals(name);
    }

    private boolean isMissingRequiredArgument() {
      return REQUIRED_ARGUMENT_NAMES.contains(this.name) && this.argument().isEmpty();
    }

    private String argument() {
      return this.rawArgument.trim();
    }

    private String text() {
      return this.rawArgument.isEmpty() ? this.name : this.name + " " + this.rawArgument;
    }
  }

  private static final List<Canonicalization> MODIFIER_CANONICALIZATIONS =
      List.of(
          tokenCanonicalization("mus", "muscle"),
          tokenCanonicalization("mys(t(ical(ity)?)?)?", "mysticality"),
          tokenCanonicalization("mox", "moxie"),
          tokenCanonicalization("res", "resistance"),
          tokenCanonicalization("dmg", "damage"),
          tokenCanonicalization("exp", "experience"),
          tokenCanonicalization("perc(ent(age)?)?", "percent"),
          canonicalization("organ", "organ capacity"),
          canonicalization("(any|ele) resistance", "elemental resistance"),
          canonicalization("main", "mainstat"),
          canonicalization("com", "combat"),
          canonicalization("init", DoubleModifier.INITIATIVE.getName()),
          canonicalization("hp", DoubleModifier.HP.getName()),
          canonicalization("mp", DoubleModifier.MP.getName()),
          canonicalization("da", DoubleModifier.DAMAGE_ABSORPTION.getName()),
          canonicalization("dr", DoubleModifier.DAMAGE_REDUCTION.getName()),
          canonicalization("ml", DoubleModifier.MONSTER_LEVEL.getName()),
          canonicalization("item", DoubleModifier.ITEMDROP.getName()),
          canonicalization("meat", DoubleModifier.MEATDROP.getName()),
          canonicalization("crit(ical)?", DoubleModifier.CRITICAL_PCT.getName()),
          canonicalization("spell crit(ical)?", DoubleModifier.SPELL_CRITICAL_PCT.getName()),
          canonicalization("sprinkle", DoubleModifier.SPRINKLES.getName()),
          canonicalization("stomach", DoubleModifier.STOMACH_CAPACITY.getName()),
          canonicalization("liver", DoubleModifier.LIVER_CAPACITY.getName()),
          canonicalization("spleen", DoubleModifier.SPLEEN_CAPACITY.getName()));

  private static final Map<String, String> DIRECTIVE_ALIASES =
      Map.of(
          "handed", "hand",
          "hands", "hand",
          "tiebreaker", "tie",
          "stinky cheese", "stinkycheese");

  private static Canonicalization tokenCanonicalization(String pattern, String canonical) {
    return new Canonicalization(Pattern.compile("\\b(?:" + pattern + ")\\b"), canonical);
  }

  private static Canonicalization canonicalization(String pattern, String canonical) {
    return new Canonicalization(Pattern.compile("^(?:" + pattern + ")$"), canonical);
  }

  private static String canonicalizeModifierName(String name) {
    for (var canonicalization : MODIFIER_CANONICALIZATIONS) {
      name = canonicalization.pattern().matcher(name).replaceAll(canonicalization.canonical());
    }
    return name;
  }

  static final Pattern TERM_PATTERN =
      Pattern.compile(
          "\\G\\s*(\\+|-|)([\\d.]*)\\s*(\"[^\"]+\"|(?:[^-+,0-9]|(?<! )[-+0-9])+),?\\s*");

  MaximizerExpression() {
    for (var modifier : DoubleModifier.DOUBLE_MODIFIERS) {
      this.min.put(modifier, Double.NEGATIVE_INFINITY);
      this.max.put(modifier, Double.POSITIVE_INFINITY);
    }
    for (var modifier : OSITY_MODIFIERS) {
      this.min.put(modifier, Double.NEGATIVE_INFINITY);
      this.max.put(modifier, Double.POSITIVE_INFINITY);
    }
  }

  @SuppressWarnings("BooleanMethodIsAlwaysInverted")
  private boolean forceModeable(ItemFinder.ItemWithMode modeable, String mode) {
    String existing = this.forcedModeables.get(modeable.modeable());
    if (!existing.isEmpty() && !existing.equals(mode)) {
      KoLmafia.updateDisplay(
          MafiaState.ERROR,
          "Conflicting modes requested for "
              + modeable.item().getName()
              + ": "
              + existing
              + " vs "
              + mode);
      return false;
    }
    this.forcedModeables.put(modeable.modeable(), mode);
    return true;
  }

  void parse(String expression) {
    expression = expression.trim().toLowerCase();
    Matcher matcher = TERM_PATTERN.matcher(expression);
    boolean hadFamiliar = false;
    boolean forceCurrent = false;
    int position = 0;
    Modifier index = null;

    int equipBeeosity = 0;
    int outfitBeeosity = 0;

    while (position < expression.length()) {
      if (!matcher.find()) {
        KoLmafia.updateDisplay(
            MafiaState.ERROR, "Unable to interpret: " + expression.substring(position));
        return;
      }
      position = matcher.end();
      double weight =
          StringUtilities.parseDouble(
              matcher.end(2) == matcher.start(2)
                  ? matcher.group(1) + "1"
                  : matcher.group(1) + matcher.group(2));

      Directive directive = Directive.parse(matcher.group(3).trim());
      if (directive.isMissingRequiredArgument()) {
        KoLmafia.updateDisplay(MafiaState.ERROR, "Unrecognized keyword: " + directive.text());
        return;
      }

      if (directive.is("min")) {
        if (index != null) {
          this.min.put(index, weight);
        } else {
          this.totalMin = weight;
        }
        continue;
      }

      if (directive.is("max")) {
        if (index != null) {
          this.max.put(index, weight);
        } else {
          this.totalMax = weight;
        }
        continue;
      }

      index = null;

      if (directive.is("dump")) {
        this.dump = (int) weight;
        continue;
      }

      if (directive.is("hand")) {
        this.hands = (int) weight;
        continue;
      }

      if (directive.is("tie")) {
        this.noTiebreaker = weight < 0.0;
        continue;
      }

      if (directive.is("current")) {
        this.current = weight > 0.0;
        forceCurrent = true;
        continue;
      }

      if (directive.is("type")) {
        this.weaponType = directive.argument();
        continue;
      }

      if (directive.is("club")) {
        this.requireClub = weight > 0.0;
        continue;
      }

      if (directive.is("shield")) {
        this.requireShield = weight > 0.0;
        if (this.forcedModeables.get(Modeable.UMBRELLA).isEmpty()) {
          this.forcedModeables.put(Modeable.UMBRELLA, "forward-facing");
        }
        this.hands = 1;
        continue;
      }

      if (directive.is("utensil")) {
        this.requireUtensil = weight > 0.0;
        continue;
      }
      if (directive.is("sword")) {
        this.requireSword = weight > 0.0;
        continue;
      }

      if (directive.is("knife")) {
        this.requireKnife = weight > 0.0;
        continue;
      }

      if (directive.is("accordion")) {
        this.requireAccordion = weight > 0.0;
        continue;
      }

      if (directive.is("melee")) {
        this.melee = (int) (weight * 2.0);
        continue;
      }

      if (directive.is("effective")) {
        this.effective = weight > 0.0;
        continue;
      }

      if (directive.is("empty")) {
        for (var slot : SlotSet.ALL_SLOTS) {
          this.slots.merge(
              slot,
              ((int) weight)
                  * (EquipmentManager.getEquipment(slot).equals(EquipmentRequest.UNEQUIP) ? 1 : -1),
              Integer::sum);
        }
        continue;
      }

      BitmapModifier osityModifier = null;
      double defaultMinimum = 0.0;
      double defaultMaximum = 0.0;
      switch (directive.name()) {
        case "clownosity", "clowniness" -> {
          osityModifier = BitmapModifier.CLOWNINESS;
          defaultMinimum = 100.0;
          defaultMaximum = 100.0;
        }
        case "raveosity" -> {
          osityModifier = BitmapModifier.RAVEOSITY;
          defaultMinimum = 7.0;
          defaultMaximum = 7.0;
        }
        case "surgeonosity" -> {
          osityModifier = BitmapModifier.SURGEONOSITY;
          defaultMinimum = 1.0;
          defaultMaximum = 5.0;
        }
      }
      if (osityModifier != null) {
        index = osityModifier;
        this.weight.put(osityModifier, weight);
        this.min.put(osityModifier, defaultMinimum);
        this.max.put(osityModifier, defaultMaximum);
        continue;
      }

      if (directive.is("beeosity")) {
        this.beeosity = (int) weight;
        continue;
      }

      if (directive.is("stinkycheese")) {
        this.stinkycheese = (int) weight;
        continue;
      }

      if (directive.is("sea")) {
        var adventureUnderwater =
            EnumSet.of(BooleanModifier.ADVENTURE_UNDERWATER, BooleanModifier.UNDERWATER_FAMILIAR);
        this.booleanMask.addAll(adventureUnderwater);
        this.booleanValue.addAll(adventureUnderwater);
        index = null;
        if (this.forcedModeables.get(Modeable.EDPIECE).isEmpty()) {
          this.forcedModeables.put(Modeable.EDPIECE, "fish");
        }
        continue;
      }

      if (directive.is("equip")) {
        var match = ItemFinder.getFirstMatchingItemWithMode(directive.argument(), Match.EQUIP);
        if (match == null) {
          return;
        }
        if (match.modeable() != null && !this.forceModeable(match, match.mode())) {
          return;
        }
        if (weight > 0.0) {
          if (this.posEquip.add(match.item())) {
            equipBeeosity += KoLCharacter.getBeeosity(match.item().getName());
          }
        } else {
          this.negEquip.add(match.item());
        }
        continue;
      }

      if (directive.is("bonus")) {
        var match = ItemFinder.getFirstMatchingItemWithMode(directive.argument(), Match.EQUIP);
        if (match == null) {
          return;
        }
        if (match.mode() == null) {
          var existing = this.bonuses.get(match.item());
          var modes = existing == null ? new HashMap<String, Double>() : existing.modes();
          this.bonuses.put(match.item(), new ItemBonus(weight, modes));
        } else {
          this.bonuses
              .computeIfAbsent(match.item(), item -> new ItemBonus(0.0, new HashMap<>()))
              .modes()
              .put(match.mode(), weight);
        }
        continue;
      }

      if (directive.is("modbonus")) {
        String modName = directive.rawArgument();
        BooleanModifier mod = BooleanModifier.byCaselessName(modName);
        if (mod == null) {
          KoLmafia.updateDisplay(MafiaState.ERROR, "No boolean modifier found for: " + modName);
          return;
        }
        this.modBonuses.put(mod, weight);
        continue;
      }

      if (directive.is("letter")) {
        String argument = directive.argument();
        if (argument.isEmpty()) {
          this.bonusFunc.add(new BonusFunction(LetterBonus::letterBonus, weight));
        } else {
          this.bonusFunc.add(
              new BonusFunction(item -> LetterBonus.letterBonus(item, argument), weight));
        }
        continue;
      }

      if (directive.is("number")) {
        this.bonusFunc.add(new BonusFunction(LetterBonus::numberBonus, weight));
        continue;
      }

      if (directive.is("plumber")) {
        if (!KoLCharacter.isPlumber()) {
          KoLmafia.updateDisplay(MafiaState.ERROR, "You are not a Plumber");
          return;
        }
        AdventureResult item = this.pickPlumberTool(KoLCharacter.getPrimeIndex());
        if (item == null) {
          item = this.pickPlumberTool(-1);
        }
        this.posEquip.add(item);
        continue;
      }

      if (directive.is("cold plumber")) {
        if (!KoLCharacter.isPlumber()) {
          KoLmafia.updateDisplay(MafiaState.ERROR, "You are not a Plumber");
          return;
        }
        AdventureResult item1 = this.pickPlumberTool(1);
        if (item1 == null) {
          KoLmafia.updateDisplay(MafiaState.ERROR, "You don't have an appropriate flower to wield");
          return;
        }
        AdventureResult item2 = ItemPool.get(ItemPool.FROSTY_BUTTON);
        this.posEquip.add(item1);
        this.posEquip.add(item2);
        continue;
      }

      if (directive.is("outfit")) {
        String outfitName = directive.argument();
        if (outfitName.isEmpty()) {
          outfitName = KoLCharacter.currentStringModifier(StringModifier.OUTFIT);
        }
        SpecialOutfit outfit = EquipmentManager.getMatchingOutfit(outfitName);
        if (outfit == null || outfit.getOutfitId() <= 0) {
          KoLmafia.updateDisplay(MafiaState.ERROR, "Unknown or custom outfit: " + outfitName);
          return;
        }
        if (weight > 0.0) {
          this.posOutfits.add(outfit.getName());
          int bees = 0;
          for (AdventureResult piece : outfit.getPieces()) {
            bees += KoLCharacter.getBeeosity(piece.getName());
          }
          outfitBeeosity = Math.max(outfitBeeosity, bees);
        } else {
          this.negOutfits.add(outfit.getName());
        }
        continue;
      }

      if (directive.is("switch")) {
        if (KoLCharacter.inPokefam()) {
          continue;
        }
        String familiarName = directive.argument();
        int id = FamiliarDatabase.getFamiliarId(familiarName);
        if (id == -1) {
          KoLmafia.updateDisplay(MafiaState.ERROR, "Unknown familiar: " + familiarName);
          return;
        }
        if (hadFamiliar && weight < 0.0) continue;
        FamiliarData familiar = KoLCharacter.usableFamiliar(id);
        if (familiar == null && weight > 1.0) {
          familiar = new FamiliarData(id);
          familiar.setWeight((int) weight);
        }
        hadFamiliar = familiar != null;
        if (familiar != null
            && !familiar.equals(KoLCharacter.getFamiliar())
            && familiar.canEquip()
            && !this.familiars.contains(familiar)) {
          this.familiars.add(familiar);
        }
        continue;
      }

      Slot slot = EquipmentRequest.slotNumber(directive.text());
      if (SlotSet.ALL_SLOTS.contains(slot)) {
        this.slots.merge(slot, (int) weight, Integer::sum);
        continue;
      }

      String modifierName = canonicalizeModifierName(directive.text());
      index = DoubleModifier.byCaselessName(modifierName);

      if (index == null) {
        BooleanModifier modifier = BooleanModifier.byCaselessName(modifierName);
        if (modifier != null) {
          this.booleanMask.add(modifier);
          if (weight > 0.0) {
            this.booleanValue.add(modifier);
          }
          continue;
        }
      }

      if (index == null) {
        switch (modifierName) {
          case "elemental resistance" -> {
            this.weight.put(DoubleModifier.COLD_RESISTANCE, weight);
            this.weight.put(DoubleModifier.HOT_RESISTANCE, weight);
            this.weight.put(DoubleModifier.SLEAZE_RESISTANCE, weight);
            this.weight.put(DoubleModifier.SPOOKY_RESISTANCE, weight);
            this.weight.put(DoubleModifier.STENCH_RESISTANCE, weight);
            continue;
          }
          case "elemental damage" -> {
            this.weight.put(DoubleModifier.COLD_DAMAGE, weight);
            this.weight.put(DoubleModifier.HOT_DAMAGE, weight);
            this.weight.put(DoubleModifier.SLEAZE_DAMAGE, weight);
            this.weight.put(DoubleModifier.SPOOKY_DAMAGE, weight);
            this.weight.put(DoubleModifier.STENCH_DAMAGE, weight);
            continue;
          }
          case "hp regen" -> {
            this.weight.put(DoubleModifier.HP_REGEN_MIN, weight / 2);
            this.weight.put(DoubleModifier.HP_REGEN_MAX, weight / 2);
            continue;
          }
          case "mp regen" -> {
            this.weight.put(DoubleModifier.MP_REGEN_MIN, weight / 2);
            this.weight.put(DoubleModifier.MP_REGEN_MAX, weight / 2);
            continue;
          }
          case "passive damage" -> {
            this.weight.put(DoubleModifier.DAMAGE_AURA, weight);
            this.weight.put(DoubleModifier.THORNS, weight);
            continue;
          }
          case "organ capacity" -> {
            this.weight.put(DoubleModifier.STOMACH_CAPACITY, weight);
            this.weight.put(DoubleModifier.LIVER_CAPACITY, weight);
            this.weight.put(DoubleModifier.SPLEEN_CAPACITY, weight);
            continue;
          }
        }
      }

      if (index == null) {
        if (modifierName.equals("mainstat")) {
          index = DoubleModifier.primeStat();
        } else if (modifierName.equals("combat")) {
          index = DoubleModifier.COMBAT_RATE;
          if (AdventureDatabase.isUnderwater(Modifiers.currentLocation)) {
            this.weight.put(DoubleModifier.UNDERWATER_COMBAT_RATE, weight);
          }
        } else if (modifierName.equals("adv")) {
          this.beeosity = 999;
          index = DoubleModifier.ADVENTURES;
        } else if (modifierName.equals("fites")) {
          this.beeosity = 999;
          index = DoubleModifier.PVP_FIGHTS;
        } else if (modifierName.equals("ocrs")) {
          this.noTiebreaker = true;
          this.beeosity = 999;
          index = DoubleModifier.RANDOM_MONSTER_MODIFIERS;
        }
      }

      if (index != null) {
        this.weight.put(index, weight);
        continue;
      }

      KoLmafia.updateDisplay(MafiaState.ERROR, "Unrecognized keyword: " + directive.text());
      return;
    }

    if (!forceCurrent && this.noTiebreaker) {
      this.current = true;
    }

    this.beeosity = Math.max(Math.max(this.beeosity, equipBeeosity), outfitBeeosity);

    this.addFudge(
        DoubleModifier.EXPERIENCE,
        DoubleModifier.MONSTER_LEVEL,
        DoubleModifier.MONSTER_LEVEL_PERCENT,
        DoubleModifier.MUS_EXPERIENCE,
        DoubleModifier.MYS_EXPERIENCE,
        DoubleModifier.MOX_EXPERIENCE,
        DoubleModifier.MUS_EXPERIENCE_PCT,
        DoubleModifier.MYS_EXPERIENCE_PCT,
        DoubleModifier.MOX_EXPERIENCE_PCT,
        DoubleModifier.VOLLEYBALL_WEIGHT,
        DoubleModifier.SOMBRERO_WEIGHT,
        DoubleModifier.VOLLEYBALL_EFFECTIVENESS,
        DoubleModifier.SOMBRERO_EFFECTIVENESS,
        DoubleModifier.SOMBRERO_BONUS);

    this.addFudge(
        DoubleModifier.ITEMDROP,
        DoubleModifier.FOODDROP,
        DoubleModifier.BOOZEDROP,
        DoubleModifier.HATDROP,
        DoubleModifier.WEAPONDROP,
        DoubleModifier.OFFHANDDROP,
        DoubleModifier.SHIRTDROP,
        DoubleModifier.PANTSDROP,
        DoubleModifier.ACCESSORYDROP,
        DoubleModifier.CANDYDROP,
        DoubleModifier.GEARDROP,
        DoubleModifier.FAIRY_WEIGHT,
        DoubleModifier.FAIRY_EFFECTIVENESS,
        DoubleModifier.SPORADIC_ITEMDROP,
        DoubleModifier.PICKPOCKET_CHANCE);

    this.addFudge(
        DoubleModifier.MEATDROP,
        DoubleModifier.LEPRECHAUN_WEIGHT,
        DoubleModifier.LEPRECHAUN_EFFECTIVENESS,
        DoubleModifier.SPORADIC_MEATDROP,
        DoubleModifier.MEAT_BONUS);

    this.addFudge(DoubleModifier.DAMAGE_AURA, DoubleModifier.SPORADIC_DAMAGE_AURA);
    this.addFudge(DoubleModifier.THORNS, DoubleModifier.SPORADIC_THORNS);
  }

  private void addFudge(DoubleModifier source, DoubleModifier... extras) {
    final double fudge = this.weight.getOrDefault(source, 0.0) * 0.0001f;
    if (fudge > 0) {
      for (var extra : extras) {
        this.weight.merge(extra, fudge, Double::sum);
      }
    }
  }

  private AdventureResult pickPlumberTool(int primeIndex) {
    AdventureResult hammer = ItemPool.get(ItemPool.HAMMER);
    boolean haveHammer = InventoryManager.hasItem(hammer);
    AdventureResult heavyHammer = ItemPool.get(ItemPool.HEAVY_HAMMER);
    boolean haveHeavyHammer = InventoryManager.hasItem(heavyHammer);
    AdventureResult fireFlower = ItemPool.get(ItemPool.PLUMBER_FIRE_FLOWER);
    boolean haveFireFlower = InventoryManager.hasItem(fireFlower);
    AdventureResult bonfireFlower = ItemPool.get(ItemPool.BONFIRE_FLOWER);
    boolean haveBonfireFlower = InventoryManager.hasItem(bonfireFlower);
    AdventureResult workBoots = ItemPool.get(ItemPool.WORK_BOOTS);
    boolean haveWorkBoots = InventoryManager.hasItem(workBoots);
    AdventureResult fancyBoots = ItemPool.get(ItemPool.FANCY_BOOTS);
    boolean haveFancyBoots = InventoryManager.hasItem(fancyBoots);

    return switch (primeIndex) {
      case 0 -> haveHeavyHammer ? heavyHammer : haveHammer ? hammer : null;
      case 1 -> haveBonfireFlower ? bonfireFlower : haveFireFlower ? fireFlower : null;
      case 2 -> haveFancyBoots ? fancyBoots : haveWorkBoots ? workBoots : null;
      default ->
          haveHeavyHammer
              ? heavyHammer
              : haveBonfireFlower
                  ? bonfireFlower
                  : haveFancyBoots
                      ? fancyBoots
                      : haveHammer ? hammer : haveFireFlower ? fireFlower : workBoots;
    };
  }
}
