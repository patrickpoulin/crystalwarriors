"""Crystal Warriors (Game Gear) text editor.

  python tools/cwtext.py extract   -> writes the text files in text/ from the original game
  python tools/cwtext.py build     -> applies every file in text/, writes crystalwarrior-mod.gg

The original crystalwarrior.gg is never modified.
"""
import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ROM = ROOT / "crystalwarrior.gg"
TEXT_DIR = ROOT / "text"
BATTLE_FILE = TEXT_DIR / "battle-text.txt"
STORY_FILE = TEXT_DIR / "story-text.txt"
UNITS_FILE = TEXT_DIR / "units.txt"
MOD = ROOT / "crystalwarrior-mod.gg"

# ---- the game's character set ----
PUNCT = {0x00: " ", 0x26: "!", 0x27: "'", 0x28: "(", 0x29: ")", 0x2A: ",", 0x2C: ".",
         0x32: "?", 0x33: ":", 0x34: '"'}
TOKENS = {0xFB: "{NAME}", 0xFC: "{NUM}", 0xF8: "{SPELL}", 0xFE: "{NL}", 0xF9: "{WAIT}"}
END = 0xFF

DECODE = {**PUNCT, **TOKENS}
for i in range(26):
    DECODE[0x0B + i] = chr(65 + i)
for i in range(10):
    DECODE[0x01 + i] = str(i)
ENCODE_CHAR = {v: k for k, v in DECODE.items() if len(v) == 1}
ENCODE_TOKEN = {v[1:-1]: k for k, v in TOKENS.items()}

# ---- where the text lives ----
BATTLE_START, BATTLE_END = 0x190C8, 0x194D8   # in-battle message table (bank 6)
VERDICT_TABLE = 0x33EC0                       # 8 records: vram(2) width height ptr(2) pad(2)
VERDICT_NAMES = ["stunning victory", "won", "barely won", "miracle win",
                 "slaughtered", "lost", "almost won", "how could you lose"]
LINE_WARN = 14                                # widest line the original text box uses
STORY_TABLE = 0x7672                          # 4 pointers; entry 0 = new game, 1-3 share one passage
STORY_WIDTH = 14                              # the story box is exactly 14 characters wide
NAME_TABLE, NAME_SLOT, NAME_MAX = 0xAF7F, 14, 5  # 13-byte name slots + FF; name ends with FA
NAME_END = 0xFA
UNIT_COUNT = 55                               # 0-16 your army, 17-33 opponents, 34-38 bosses, 39-54 monsters
CLASS_TABLE = 0x169FE                         # one byte per unit (a second copy the game keeps)
ELEMENT_TABLE = CLASS_TABLE + UNIT_COUNT      # one byte per unit (a second copy the game keeps)
STATUS_CLASS_PTRS = 0x6777                    # status screen: pointer to class word, units 0-38
STATUS_CLASS_COUNT = 39
STATUS_ELEM_PTRS = STATUS_CLASS_PTRS + 2 * STATUS_CLASS_COUNT   # pointer to element word, all units
STATUS_WORDS = 0x6833                         # PRINCESS LORD ... MONSTER EARTH FIRE WIND WATER
CLASS_CODES = {0: "PRINCESS", 1: "MAGE", 2: "LORD", 3: "RANGER", 4: "FIGHTER", 5: "HEALER",
               6: "EMPEROR", 7: "WARLORD", 8: "WARLORD", 9: "WARLORD", 10: "WIZARD", 11: "MONSTER"}
ELEMENT_CODES = {0: "NEUTRAL", 1: "EARTH", 2: "WATER", 3: "FIRE", 4: "WIND"}
GROWTH_TABLE = 0x22D21                        # pointers to per-level rows of 6 classes x 5 stats
GROWTH_CLASSES = ["PRINCESS", "LORD", "FIGHTER", "RANGER", "MAGE", "HEALER"]
GROWTH_LEVELS = 8
# SP (movement) isn't stored per unit: the unit setup code at 0x11B6 picks one of
# four constants by unit id. Each entry: (name, file offset of the constant, who gets it)
SP_GROUPS = [("PRINCESSES_HEALERS_MAGES", 0x11DC, "units 0, 13-16 (and 17, 30-33)"),
             ("LORDS_FIGHTERS_RANGERS", 0x11D8, "units 1-12 (and 18-29)"),
             ("JYN_AND_WARLORDS", 0x11C5, "units 34-37"),
             ("GRYM_AND_MONSTERS", 0x11C9, "units 38-54")]
SP_MAX = 15
# Starting army for NEW ADVENTURE: count, then per unit [id, 3 setup bytes, n, spell ids...].
# Loaded by LD HL,nnnn at 0x6B47 (pointer bytes at 0x6B48). If edits make it longer, it moves into unused space.
ARMY_LIST, ARMY_PTR = 0x238BC, 0x6B48
ARMY_FREE, ARMY_FREE_END = 0x23990, 0x24000  # FF filler at the end of bank 8
SPELL_TABLE = 0xAF51 + 2 * 8                  # 15 pointers to spell names (after the unit-name pointers)
SPELL_COUNT, SPELL_SLOTS = 15, 4              # spell ids are 1-15; a unit holds up to 4
STORY_NAMES = {0: "shown when you start a NEW ADVENTURE",
               1: "the minstrel's short tale (used by the other story slots)"}


def decode(bs):
    return "".join(DECODE.get(b, "{%02X}" % b) for b in bs)


def encode(s, where):
    out, i = [], 0
    while i < len(s):
        if s[i] == "{":
            j = s.find("}", i)
            if j < 0:
                raise ValueError(f"{where}: missing '}}'")
            tok = s[i + 1:j].upper()
            if tok in ENCODE_TOKEN:
                out.append(ENCODE_TOKEN[tok])
            elif re.fullmatch(r"[0-9A-F]{2}", tok):
                out.append(int(tok, 16))
            else:
                raise ValueError(f"{where}: unknown code {{{tok}}}")
            i = j + 1
        else:
            c = s[i].upper()
            if c not in ENCODE_CHAR:
                raise ValueError(f"{where}: the game has no '{s[i]}' character "
                                 f"(allowed: A-Z 0-9 space ! ' ( ) , . ? : \")")
            out.append(ENCODE_CHAR[c])
            i += 1
    return bytes(out)


def bank_ptr(offset):
    return 0x8000 + (offset % 0x4000)


def battle_messages(rom):
    """(offset, raw bytes without the FF terminator) for each message."""
    msgs, i = [], BATTLE_START
    while i < BATTLE_END:
        j = rom.index(END, i)
        msgs.append((i, rom[i:j]))
        i = j + 1
    return msgs


def has_code_pointer(rom, offset):
    """True when some LD HL/DE/BC,nn instruction loads this message's address."""
    p = bank_ptr(offset)
    pat = bytes([p & 0xFF, p >> 8])
    k = rom.find(pat)
    while k >= 0:
        if k > 0 and rom[k - 1] in (0x21, 0x11, 0x01):
            return True
        k = rom.find(pat, k + 1)
    return False


def verdicts(rom):
    out = []
    for n in range(8):
        r = rom[VERDICT_TABLE + 8 * n: VERDICT_TABLE + 8 * n + 8]
        w, h, p = r[2], r[3], r[4] | r[5] << 8
        off = (VERDICT_TABLE & ~0x3FFF) + (p - 0x8000)
        out.append((n, off, w, h))
    return out


def stories(rom):
    """(n, offset, raw bytes without FF) for each distinct story passage."""
    out, seen = [], set()
    for k in range(4):
        off = rom[STORY_TABLE + 2 * k] | rom[STORY_TABLE + 2 * k + 1] << 8   # bank 2 sits at 0x8000
        if off not in seen:
            seen.add(off)
            out.append((len(out), off, rom[off:rom.index(END, off)]))
    return out


# ---------------------------------------------------------------- extract
HEADER = """\
# Crystal Warriors - battle text
#
# Edit the lines below, then run:   python tools/cwtext.py build
# That writes crystalwarrior-mod.gg (your original game file is never changed).
#
# RULES
#  - Capital letters, numbers, space and  ! ' ( ) , . ? : "  only. (Lowercase is
#    turned into capitals - the game has no lowercase letters.)
#  - A message can be shorter than the original but not longer. The [max N]
#    tag is the limit in bytes: each letter is 1, each {CODE} is 1.
#  - Codes the game fills in or acts on:
#      {NAME}  unit name      {NUM}  a number      {SPELL}  spell name
#      {NL}    new line       {WAIT} wait for the button before continuing
#      {35} etc. are symbols whose meaning isn't known yet - keep them.
#  - The text box fits about 14 characters per line, 2 lines per message.
#  - Lines starting with # are notes and are ignored. "was:" shows the original.
"""

STORY_HEADER = """\
# Crystal Warriors - opening story
#
# Edit the lines below, then run:   python tools/cwtext.py build
#
# Each |...| row is one line on screen. The story box shows 8 rows and scrolls,
# so you can use as many rows as you like, but:
#  - a row can be at most 14 characters (the width of the bars below)
#  - the whole passage can't be longer than the original: [max N] counts every
#    character plus 1 for each row break
#  - a row with nothing between the bars is a blank line (paragraph break)
#  - Capital letters, numbers, space and  ! ' ( ) , . ? : "  only
#  - Lines starting with # are notes and are ignored.
"""


def write_battle_file(rom):
    lines = [HEADER]
    lines.append("\n# ===================== BATTLE MESSAGES =====================")
    lines.append("# The after-battle summary is near the end (THE BATTLE IS UNRESOLVED onward).\n")
    for off, raw in battle_messages(rom):
        lines.append(f"[{off:05X}] max {len(raw)}")
        lines.append(f"#   was: {decode(raw)}")
        lines.append(decode(raw))
        lines.append("")
    lines.append("# ===================== END-OF-BATTLE VERDICTS =====================")
    lines.append("# Each verdict is a fixed box: type inside the | | bars, rows can't get wider.\n")
    for n, off, w, h in verdicts(rom):
        raw = rom[off:off + w * h]
        lines.append(f"[VERDICT {n}] {w} wide x {h} rows   ({VERDICT_NAMES[n]})")
        for r in range(h):
            lines.append("|" + decode(raw[r * w:(r + 1) * w]) + "|")
        lines.append("")
    BATTLE_FILE.write_text("\n".join(lines), encoding="utf-8")


def write_story_file(rom):
    lines = [STORY_HEADER]
    for n, off, raw in stories(rom):
        lines.append(f"[STORY {n}] max {len(raw)}   ({STORY_NAMES.get(n, '')})")
        for row in raw.split(bytes([0xFE])):
            lines.append("|" + decode(row).ljust(STORY_WIDTH) + "|")
        lines.append("")
    STORY_FILE.write_text("\n".join(lines), encoding="utf-8")


UNITS_HEADER = """\
# Crystal Warriors - units and class stats
#
# Edit, then run:   python tools/cwtext.py build
#
# UNITS: one line per unit:  id  NAME  CLASS  ELEMENT
#  - Names: 1 to 5 characters (capitals, numbers, ! ' ( ) , . ? : ").
#  - CLASS is shown for reference only and can't be changed yet.
#  - Elements: EARTH FIRE WIND WATER. (Changing one updates the status screen;
#    whether battles use the new element hasn't been tested yet.)
#  - Bosses (34-38) and monsters (39-54): names and elements only - their stats
#    aren't mapped yet.
#  - Ids 0-16 are your army. 17-33 are the opposing army (2-player mode, led by CHAM).
#
# CLASS STATS: HP MP AP DP LK at each level, shared by every unit of that class.
#  - Values 0-255. A level-up gives the difference between two rows.
#  - Only levels 1-8 are listed; level 9 isn't fully understood yet.
"""


def unit_names(rom):
    out = []
    for n in range(UNIT_COUNT):
        raw = rom[NAME_TABLE + NAME_SLOT * n: NAME_TABLE + NAME_SLOT * n + NAME_SLOT - 1]
        out.append(decode(raw[:raw.index(NAME_END)]))
    return out


def status_words(rom):
    """{word: address} for the status screen's class and element words."""
    words, i = {}, STATUS_WORDS
    for _ in range(15):
        j = rom.index(END, i)
        words[decode(rom[i:j])] = i
        i = j + 1
    return words


def status_class_elem(rom, n):
    """(class, element) as the status screen shows them for unit n."""
    by_addr = {a: w for w, a in status_words(rom).items()}
    ptr = lambda at: rom[at] | rom[at + 1] << 8
    cls = by_addr[ptr(STATUS_CLASS_PTRS + 2 * n)] if n < STATUS_CLASS_COUNT else "MONSTER"
    return cls, by_addr[ptr(STATUS_ELEM_PTRS + 2 * n)]


def spell_names(rom):
    """['SCAN', 'HEAL', ...] - index 0 is spell id 1."""
    out = []
    for k in range(SPELL_COUNT):
        p = rom[SPELL_TABLE + 2 * k] | rom[SPELL_TABLE + 2 * k + 1] << 8
        off = (NAME_TABLE & ~0x3FFF) + (p - 0x8000)
        out.append(decode(rom[off:rom.index(NAME_END, off)]).strip())
    return out


def starting_army(rom):
    """[(unit id, setup bytes, [spell ids])] for the NEW ADVENTURE army."""
    p = rom[ARMY_PTR] | rom[ARMY_PTR + 1] << 8
    i = (ARMY_LIST & ~0x3FFF) + (p - 0x8000)
    units, i = [], i + 1
    for _ in range(rom[i - 1]):
        n = rom[i + 4]
        units.append((rom[i], rom[i + 1:i + 4], list(rom[i + 5:i + 5 + n])))
        i += 5 + n
    return units


def growth_rows(rom):
    """Offset of each level's row (6 classes x HP MP AP DP LK)."""
    rows = []
    for lv in range(GROWTH_LEVELS):
        p = rom[GROWTH_TABLE + 2 * lv] | rom[GROWTH_TABLE + 2 * lv + 1] << 8
        rows.append((GROWTH_TABLE & ~0x3FFF) + (p - 0x8000))
    return rows


def write_units_file(rom):
    lines = [UNITS_HEADER, "# ===================== UNITS =====================",
             "# id  NAME   CLASS     ELEMENT"]
    names = unit_names(rom)
    for n in range(UNIT_COUNT):
        if n in (0, 17, 34, 39):
            lines.append({0: "\n# --- your army ---", 17: "\n# --- opposing army ---",
                          34: "\n# --- Jyn bosses ---", 39: "\n# --- monsters ---"}[n])
        cls, el = status_class_elem(rom, n)
        lines.append(f"{n:4d}  {names[n]:<6} {cls:<9} {el}")
    lines.append("\n# ===================== MOVEMENT (SP) =====================")
    lines.append("# SP = how far a unit can move each turn. The game sets it by group, not per unit,")
    lines.append(f"# so each number below applies to everyone in that group. Values 1-{SP_MAX}.")
    lines.append("\n[MOVEMENT]")
    for name, off, who in SP_GROUPS:
        lines.append(f"  {name:<26} {rom[off]:2d}    # {who}")
    lines.append("\n# ===================== STARTING SPELLS =====================")
    lines.append("# Spells each unit knows when you start a NEW ADVENTURE (saved books keep theirs).")
    lines.append(f"# Up to {SPELL_SLOTS} per unit, or NONE. The name column is only a reminder.")
    spells = spell_names(rom)
    lines.append("# Spells: " + " ".join(spells))
    lines.append("\n[STARTING SPELLS]")
    for uid, _, sp in starting_army(rom):
        lines.append(f"  {uid:2d}  {names[uid]:<6} " + (" ".join(spells[s - 1] for s in sp) or "NONE"))
    lines.append("\n# ===================== CLASS STATS =====================")
    rows = growth_rows(rom)
    for c, cname in enumerate(GROWTH_CLASSES):
        lines.append(f"\n[STATS {cname}]")
        lines.append("# LV   HP  MP  AP  DP  LK")
        for lv, off in enumerate(rows, 1):
            vals = rom[off + 5 * c: off + 5 * c + 5]
            lines.append(f"  {lv:2d}  " + " ".join(f"{v:3d}" for v in vals))
    UNITS_FILE.write_text("\n".join(lines) + "\n", encoding="utf-8")


def apply_units(orig, rom, errors):
    """Apply text/units.txt; returns how many units/levels changed."""
    if not UNITS_FILE.exists():
        return 0
    changed, section = 0, None
    rows = growth_rows(orig)
    class_ids = {v: k for k, v in CLASS_CODES.items() if k not in (8, 9)}
    elem_ids = {v: k for k, v in ELEMENT_CODES.items() if k}
    words = status_words(orig)
    army = starting_army(orig)
    army_spells = {uid: sp for uid, _, sp in army}
    spell_ids = {name: k + 1 for k, name in enumerate(spell_names(orig))}
    for ln, line in enumerate(UNITS_FILE.read_text(encoding="utf-8").splitlines(), 1):
        s = line.strip()
        if not s or s.startswith("#"):
            continue
        where = f"units.txt line {ln}"
        s = s.split("#", 1)[0].strip()
        if s.upper() in ("[MOVEMENT]", "[STARTING SPELLS]"):
            section = s.upper()[1:-1]
            continue
        m = re.fullmatch(r"\[STATS (\w+)\]", s.upper())
        if m:
            if m.group(1) not in GROWTH_CLASSES:
                errors.append(f"{where}: unknown class {m.group(1)}")
            section = m.group(1)
            continue
        parts = s.split()
        try:
            if section is None:                       # unit line
                if len(parts) != 4 or not parts[0].isdigit():
                    raise ValueError(f"{where}: expected  id NAME CLASS ELEMENT")
                n, name, cls, el = int(parts[0]), parts[1], parts[2].upper(), parts[3].upper()
                if n >= UNIT_COUNT:
                    raise ValueError(f"{where}: there is no unit {n}")
                b = encode(name, where)
                if not 1 <= len(b) <= NAME_MAX:
                    raise ValueError(f"{where}: names are 1-{NAME_MAX} characters")
                slot = NAME_TABLE + NAME_SLOT * n
                new_name = b + bytes([NAME_END]) + bytes(NAME_SLOT - 2 - len(b))
                old_cls, old_el = status_class_elem(orig, n)
                if cls not in class_ids and cls != "MONSTER":
                    raise ValueError(f"{where}: unknown class {cls}")
                if cls != old_cls:
                    # tested: the status screen relabels, but the unit keeps its old class's
                    # stats - where the real class comes from isn't mapped yet
                    raise ValueError(f"{where}: class can't be changed yet (it would only change "
                                     f"the label, not the stats) - keep {old_cls}")
                if el not in elem_ids:
                    raise ValueError(f"{where}: unknown element {el}")
                before = bytes(rom)
                rom[slot:slot + NAME_SLOT - 1] = new_name
                # the game keeps class/element twice: the status screen's word pointers
                # and a byte table; only touch them when the value actually changes
                if cls != old_cls:
                    a = words[cls]
                    rom[STATUS_CLASS_PTRS + 2 * n: STATUS_CLASS_PTRS + 2 * n + 2] = bytes([a & 0xFF, a >> 8])
                    rom[CLASS_TABLE + n] = class_ids[cls]
                if el != old_el:
                    a = words[el]
                    rom[STATUS_ELEM_PTRS + 2 * n: STATUS_ELEM_PTRS + 2 * n + 2] = bytes([a & 0xFF, a >> 8])
                    rom[ELEMENT_TABLE + n] = elem_ids[el]
                if bytes(rom) != before:
                    changed += 1
            elif section == "STARTING SPELLS":
                if len(parts) < 3 or not parts[0].isdigit():
                    raise ValueError(f"{where}: expected  id NAME SPELL...  (or NONE)")
                uid = int(parts[0])
                if uid not in army_spells:
                    raise ValueError(f"{where}: unit {uid} isn't in the starting army")
                wanted = [w.upper() for w in parts[2:]]
                if wanted == ["NONE"]:
                    wanted = []
                bad = [w for w in wanted if w not in spell_ids]
                if bad:
                    raise ValueError(f"{where}: unknown spell {bad[0]} (spells: {' '.join(spell_ids)})")
                if len(wanted) > SPELL_SLOTS:
                    raise ValueError(f"{where}: at most {SPELL_SLOTS} spells per unit")
                army_spells[uid] = [spell_ids[w] for w in wanted]
            elif section == "MOVEMENT":
                groups = {g[0]: g[1] for g in SP_GROUPS}
                if len(parts) != 2 or parts[0].upper() not in groups or not parts[1].isdigit():
                    raise ValueError(f"{where}: expected  GROUP NUMBER  (groups: {', '.join(groups)})")
                v = int(parts[1])
                if not 1 <= v <= SP_MAX:
                    raise ValueError(f"{where}: SP must be 1-{SP_MAX}")
                off = groups[parts[0].upper()]
                if rom[off] != v:
                    rom[off] = v
                    changed += 1
            else:                                     # stats row
                if len(parts) != 6 or not all(p.isdigit() for p in parts):
                    raise ValueError(f"{where}: expected  LV HP MP AP DP LK  (numbers)")
                lv, *vals = map(int, parts)
                if not 1 <= lv <= GROWTH_LEVELS:
                    raise ValueError(f"{where}: levels 1-{GROWTH_LEVELS} only")
                if any(v > 255 for v in vals):
                    raise ValueError(f"{where}: values must be 0-255")
                off = rows[lv - 1] + 5 * GROWTH_CLASSES.index(section)
                if bytes(vals) != rom[off:off + 5]:
                    rom[off:off + 5] = bytes(vals)
                    changed += 1
        except ValueError as ex:
            errors.append(str(ex))

    # rebuild the starting-army list with the (possibly) new spells
    if any(army_spells[uid] != sp for uid, _, sp in army):
        data = bytes([len(army)])
        for uid, setup, _ in army:
            sp = army_spells[uid]
            data += bytes([uid]) + setup + bytes([len(sp)] + sp)
        old_len = 1 + sum(5 + len(sp) for _, _, sp in army)
        if len(data) <= old_len:
            rom[ARMY_LIST:ARMY_LIST + len(data)] = data   # the count says where it ends
        elif ARMY_FREE + len(data) <= ARMY_FREE_END:
            rom[ARMY_FREE:ARMY_FREE + len(data)] = data
            p = 0x8000 + (ARMY_FREE % 0x4000)
            rom[ARMY_PTR:ARMY_PTR + 2] = bytes([p & 0xFF, p >> 8])
        else:
            errors.append("units.txt: starting spells don't fit")
        changed += 1
    return changed


def cmd_extract(args):
    rom = ROM.read_bytes()
    TEXT_DIR.mkdir(exist_ok=True)
    for path, writer in ((BATTLE_FILE, write_battle_file), (STORY_FILE, write_story_file),
                         (UNITS_FILE, write_units_file)):
        if path.exists() and not args.force:
            print(f"Kept {path.relative_to(ROOT)} (already exists; --force overwrites your edits)")
            continue
        writer(rom)
        print(f"Wrote {path.relative_to(ROOT)}")


# ---------------------------------------------------------------- build
def parse_text(path):
    entries, cur = [], None
    for ln, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        s = line.rstrip("\r\n")
        if not s.strip() or s.lstrip().startswith("#"):
            continue
        m = re.match(r"\[(VERDICT (\d)|STORY (\d)|([0-9A-Fa-f]{5}))\]", s.strip())
        if m:
            cur = {"line": ln, "rows": []}
            if m.group(2) is not None:
                cur["verdict"] = int(m.group(2))
            elif m.group(3) is not None:
                cur["story"] = int(m.group(3))
            else:
                cur["offset"] = int(m.group(4), 16)
            entries.append(cur)
            continue
        if cur is None:
            raise ValueError(f"line {ln}: text before any [..] header")
        cur["rows"].append((ln, s))
    return entries


def cmd_build(args):
    rom = bytearray(ROM.read_bytes())
    orig = bytes(rom)
    msgs = dict(battle_messages(orig))
    vtab = {n: (off, w, h) for n, off, w, h in verdicts(orig)}
    stab = {n: (off, raw) for n, off, raw in stories(orig)}
    errors, warnings, changed = [], [], 0

    entries = []
    for path in (BATTLE_FILE, STORY_FILE):
        if path.exists():
            entries += [dict(e, file=path.name) for e in parse_text(path)]

    for e in entries:
        try:
            if "story" in e:
                if e["story"] not in stab:
                    raise ValueError(f"{e['file']} line {e['line']}: there is no STORY {e['story']}")
                off, old = stab[e["story"]]
                rows = []
                for ln, r in e["rows"]:
                    r = r.strip()
                    if not (r.startswith("|") and r.endswith("|")):
                        raise ValueError(f"{e['file']} line {ln}: story rows must be between | bars")
                    b = encode(r[1:-1].rstrip(), f"{e['file']} line {ln}")
                    if len(b) > STORY_WIDTH:
                        raise ValueError(f"{e['file']} line {ln}: row is {len(b)} characters, max is {STORY_WIDTH}")
                    rows.append(b)
                new = bytes([0xFE]).join(rows)
                if len(new) > len(old):
                    raise ValueError(f"{e['file']} STORY {e['story']}: {len(new)} bytes, max is {len(old)} "
                                     f"- shorten by {len(new) - len(old)}")
                if new != old:
                    rom[off:off + len(old) + 1] = new + bytes([END]) * (len(old) - len(new) + 1)
                    changed += 1
            elif "verdict" in e:
                off, w, h = vtab[e["verdict"]]
                rows = [r for _, r in e["rows"]]
                if len(rows) != h:
                    raise ValueError(f"line {e['line']}: VERDICT {e['verdict']} needs exactly {h} rows")
                data = b""
                for ln, r in e["rows"]:
                    r = r.strip()
                    if not (r.startswith("|") and r.endswith("|")):
                        raise ValueError(f"line {ln}: verdict rows must be between | bars")
                    b = encode(r[1:-1].rstrip(), f"line {ln}")
                    if len(b) > w:
                        raise ValueError(f"line {ln}: row is {len(b)} wide, the box is {w}")
                    data += b + bytes(w - len(b))
                if data != orig[off:off + w * h]:
                    rom[off:off + w * h] = data
                    changed += 1
            else:
                off = e["offset"]
                if off not in msgs:
                    raise ValueError(f"line {e['line']}: [{off:05X}] is not a message start")
                if len(e["rows"]) != 1:
                    raise ValueError(f"line {e['line']}: put the whole message on one line (use {{NL}} for line breaks)")
                ln, text = e["rows"][0]
                old = msgs[off]
                new = encode(text.strip(), f"line {ln}")
                if len(new) > len(old):
                    raise ValueError(f"line {ln}: {len(new)} bytes, max is {len(old)} "
                                     f"- shorten by {len(new) - len(old)}")
                if new == old:
                    continue
                vis = re.sub(r"\{(WAIT|[0-9A-F]{2})\}", "", text.strip().upper())
                vis = vis.replace("{NAME}", "NNNNNN").replace("{NUM}", "999").replace("{SPELL}", "SSSSSS")
                parts = vis.split("{NL}")
                if any(len(p) > LINE_WARN for p in parts):
                    warnings.append(f"line {ln}: a line may be too wide for the text box (~{LINE_WARN} chars)")
                if len(parts) > 2:
                    warnings.append(f"line {ln}: more than 2 lines may not fit the text box")
                spare = len(old) - len(new)
                if spare and not has_code_pointer(orig, off):
                    # nothing points straight at this message, so keep its length exact:
                    # pad with spaces before the trailing codes
                    tail = len(new)
                    while tail and new[tail - 1] in (0xF9, 0xFE):
                        tail -= 1
                    new = new[:tail] + bytes(spare) + new[tail:]
                    warnings.append(f"line {ln}: padded with {spare} trailing space(s) to keep the length")
                    spare = 0
                rom[off:off + len(new)] = new
                rom[off + len(new)] = END
                for k in range(off + len(new) + 1, off + len(old) + 1):
                    rom[k] = END          # unused filler after the new end
                changed += 1
        except ValueError as ex:
            errors.append(str(ex))

    changed += apply_units(orig, rom, errors)

    for w in warnings:
        print("warning:", w)
    if errors:
        for er in errors:
            print("ERROR:", er)
        sys.exit(f"\n{len(errors)} problem(s) - nothing was written.")
    MOD.write_bytes(bytes(rom))
    print(f"{changed} text block(s) changed -> {MOD.name}")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    ex = sub.add_parser("extract", help="write any missing text files")
    ex.add_argument("--force", action="store_true", help="overwrite existing text files (loses your edits)")
    sub.add_parser("build", help="write crystalwarrior-mod.gg from the text files")
    args = ap.parse_args()
    {"extract": cmd_extract, "build": cmd_build}[args.cmd](args)


if __name__ == "__main__":
    main()
