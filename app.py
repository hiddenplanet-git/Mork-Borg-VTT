from flask import Flask, request, redirect, url_for, render_template_string, flash, jsonify, session, send_file, Response, abort
from datetime import datetime, timedelta
from html import escape
import io
import json
import logging
import os
import random
import re
import secrets
import unicodedata
import uuid
import zipfile

app = Flask(__name__)

# Both of these can be supplied by the environment, which is how the Docker
# setup passes them in. Editing the fallbacks here still works for a plain
# `python3 app.py` run.
app.secret_key = os.environ.get('MORKBORG_SECRET_KEY') or 'dev-secret-key-change-me'

# Reject any request body over 64KB outright
app.config['MAX_CONTENT_LENGTH'] = 64 * 1024
app.config['PERMANENT_SESSION_LIFETIME'] = timedelta(days=365)

MAX_MESSAGE_LENGTH = 300

# Players can fix or take back their own post for this long after sending.
# Posts with dice rolls can still have their text edited, but can't be
# deleted, so a roll can never be quietly removed and re-rolled.
POST_EDIT_WINDOW_SECONDS = 5 * 60
MAX_USERNAME_LENGTH = 50

# CHANGE THIS before exposing the app to anyone else
DM_PASSWORD = os.environ.get('MORKBORG_DM_PASSWORD') or 'P1zz@'

# Player logins. Every character gets a generated username/password pair the
# moment it is created, stored server-side in Characters.json so the DM can
# read them back to a player who forgets. Usernames are two grim words and a
# number; passwords skip look-alike characters (0/O, 1/l/I) so they survive
# being read aloud across the table.
USERNAME_WORDS_A = [
    'ashen', 'bleak', 'broken', 'cursed', 'dread', 'dying', 'feral', 'grim',
    'hollow', 'leaden', 'mangy', 'pale', 'rotten', 'rusted', 'sallow', 'sunken',
    'tattered', 'unclean', 'vile', 'wretched',
]
USERNAME_WORDS_B = [
    'bone', 'candle', 'crow', 'grave', 'hound', 'lantern', 'leech', 'maggot',
    'mire', 'moth', 'omen', 'raven', 'relic', 'scvm', 'skull', 'sludge',
    'thorn', 'toad', 'worm', 'wraith',
]
PASSWORD_ALPHABET = 'abcdefghjkmnpqrstuvwxyzACDEFGHJKLMNPQRTUVWXY346789'
PASSWORD_LENGTH = 10
MAX_LOGIN_FIELD_LENGTH = 64

# Failed player logins allowed per IP inside the window before further
# attempts are refused until the window rolls forward.
LOGIN_MAX_FAILURES = 10
LOGIN_FAILURE_WINDOW = timedelta(minutes=10)

# A palette tuned for the near-black MÖRK BORG page background: every entry is
# light/saturated enough to stay legible on --ink. Assigned to characters on
# creation so each player's name is visually distinct in the feed.
PLAYER_COLORS = [
    '#f2e50b', '#ff2d6f', '#ded7c4', '#5ad2f4', '#8cf24b',
    '#ff8c1a', '#c084fc', '#4ade80', '#fb7185', '#38bdf8',
    '#facc15', '#f472b6', '#a3e635', '#22d3ee', '#fdba74',
    '#e879f9', '#7dd3fc', '#fca5a5', '#bef264', '#d8b4fe',
]

# ---------------------------------------------------------------------------
# Dice roller (message board posts) — the 7 standard polyhedral dice
# ---------------------------------------------------------------------------
DICE_TYPES = {'d2': 2, 'd4': 4, 'd6': 6, 'd8': 8, 'd10': 10, 'd12': 12, 'd20': 20, 'd100': 100}
MAX_DICE_PER_TYPE = 20
MAX_ROLLS_PER_POST = 20
MAX_ROLL_LABEL_LENGTH = 24

# ---------------------------------------------------------------------------
# MÖRK BORG — Bare Bones Edition tables
# (MÖRK BORG is copyright Ockult Örtmästare Games and Stockholm Kartell.
#  This is an unofficial personal tool made under the MÖRK BORG Third Party
#  License; it is not affiliated with or endorsed by those parties.)
# ---------------------------------------------------------------------------

# Names, d6 then d8
NAMES = [
    'Aerg-Tval', 'Agn', 'Arvant', 'Belsum', 'Belum', 'Brint', 'Börda', 'Daeru',
    'Eldar', 'Felban', 'Gotven', 'Graft', 'Grin', 'Grittr', 'Haerü', 'Hargha',
    'Harmug', 'Jotna', 'Karg', 'Karva', 'Katla', 'Keftar', 'Klort', 'Kratar',
    'Kutz', 'Kvetin', 'Lygan', 'Margar', 'Merkari', 'Nagl', 'Niduk', 'Nifehl',
    'Prügl', 'Qillnach', 'Risten', 'Svind', 'Theras', 'Therg', 'Torvul', 'Törn',
    'Urm', 'Urvarg', 'Vagal', 'Vatan', 'Von', 'Vrakh', 'Vresi', 'Wemut',
]

ABILITIES = ['Agility', 'Presence', 'Strength', 'Toughness']
ABILITY_KEYS = ['agility', 'presence', 'strength', 'toughness']
ABILITY_BLURBS = {
    'Agility': 'Defend, balance, swim, flee',
    'Presence': 'Perceive, aim, charm, wield Powers',
    'Strength': 'Crush, lift, strike, grapple',
    'Toughness': 'Resist poison/cold/heat, survive falling',
}

# 3d6 sum -> ability modifier (the sum itself is never used again)
ABILITY_SCORE_TABLE = [(4, -3), (6, -2), (8, -1), (12, 0), (14, 1), (16, 2), (20, 3)]

MIN_ABILITY = -3
MAX_ABILITY = 6


def ability_from_roll(total):
    for cap, mod in ABILITY_SCORE_TABLE:
        if total <= cap:
            return mod
    return 3


# Container, d6
CONTAINERS = {
    1: 'Nothing',
    2: 'Nothing',
    3: 'Backpack (holds 7 normal-sized items)',
    4: 'Sack (holds 10 normal-sized items)',
    5: 'Small wagon',
    6: 'Donkey, not bad',
}

WEAPONS = {
    1: ('Femur', 'd4'),
    2: ('Staff', 'd4'),
    3: ('Shortsword', 'd4'),
    4: ('Knife', 'd4'),
    5: ('Warhammer', 'd6'),
    6: ('Sword', 'd6'),
    7: ('Bow', 'd6'),
    8: ('Flail', 'd8'),
    9: ('Crossbow', 'd8'),
    10: ('Zweihänder', 'd10'),
}

# tier -> (name, damage reduction, note)
ARMOR = {
    0: ('No armor (tier 0)', '', ''),
    1: ('Light armor (fur, padded cloth, leather, tier 1)', '-d2 damage', ''),
    2: ('Medium armor (scale, mail, tier 2)', '-d4 damage', 'DR+2 on Agility tests including defence'),
    3: ('Heavy armor (splint, plate, tier 3)', '-d6 damage', 'DR+4 on Agility tests, defence is DR+2'),
}

# The Powers written in scrolls, d10 each. A starting scroll is rolled on
# these so the sheet names the actual Power rather than "random scroll".
UNCLEAN_SCROLLS = [
    'Palms open the southern gate', 'Tongue of Eris', 'Te-le-kin-esis',
    'Lucy-fires levitation', 'Daemon of capillaries',
    'Nine violet signs unknot the storm', 'Metzhuotl blind your eye',
    'Foul psychompomp', 'Eyelid blinds the mind', 'Death',
]

SACRED_SCROLLS = [
    'Grace of a dead saint', 'Grace for a sinner', 'Whispers pass the gate',
    'Aegis of sorrow', 'Unmet fate', 'Bestial speech',
    "False dawn/night's chariot", 'Hermetic step',
    "Roskoe's consuming glare", 'Enochian syntax',
]

# Scrolls never work in medium/heavy armor or with a zweihänder, so a
# character who rolls a scroll in their starting kit rolls their weapon on
# d6 and their armor on d2 instead, keeping them inside what a caster can
# actually use.
SCROLL_WEAPON_DIE = 6
SCROLL_ARMOR_DIE = 2

TERRIBLE_TRAITS = [
    'Endlessly aggravated', 'Inferiority complex', 'Problems with authority', 'Loud mouth',
    'Cruel', 'Egocentric', 'Nihilistic', 'Prone to substance abuse', 'Conflicted', 'Shrewd',
    'Vindictive', 'Cowardly', 'Lazy', 'Suspicious', 'Ruthless', 'Worried', 'Bitter',
    'Deceitful', 'Wasteful', 'Arrogant',
]

BROKEN_BODIES = [
    'Staring manic gaze',
    'Covered in (for some) blasphemous tattoos',
    'Rotting face. Wears a mask',
    'Lost three toes, limps',
    'Starved: gaunt and pale',
    'One hand replaced with a rusting hook (d6 damage)',
    'Decaying teeth',
    'Hauntingly beautiful, unnervingly clean',
    'Hands caked with sores',
    'Cataracts slowly but surely spreading in both eyes',
    'Long tangled hair, at least one cockroach in residence',
    'Broken, crushed ears',
    'Juddering and stuttering from nerve damage or stress',
    'Corpulent, ravenous, drooling',
    'One hand lacks thumb and index finger, grips like a lobster',
    "Red, swollen alcoholic's nose",
    'Resting maniac face, making friends is hard',
    "Chronic athlete's foot. Stinks",
    'Recently slashed and stinking eye covered with a patch',
    'Nails cracked and black, maybe about to drop off',
]

BAD_HABITS = [
    'Obsessively collect small sharp stones',
    "Won't use a blade without testing it on your own flesh. Arms knitted with scars",
    "Can't stop drinking once you start",
    'Gambling addict. Must bet every day. If you lose, raise and bet again',
    'Cannot tolerate criticism of any kind. Results in rage and weeping',
    'Unable to get to the point. Have never actually finished a story',
    'Best friend is a skull. Carry it with you, tell it everything, you trust no one more',
    'You pick your nose so deep it bleeds',
    'Laugh hysterically at your own jokes which you then explain in detail',
    'A nihilist. You insist on telling everyone you are a nihilist and explaining why',
    'Inveterate bugeater',
    'Stress response is aesthetic display. The worse things get the fancier you need to be',
    'Permanent phlegm deposit in throat. Continuously cough, snort, spit and swallow',
    'Pyromaniac',
    'Consistently lose important items and forget vital facts',
    'Insecure shit-stirrer. Will talk about whoever just left the room',
    'You stutter when lying',
    'You giggle insanely at the worst possible times',
    'You whistle while trying to hide. You will deny this',
    'You make jewelry from the teeth of the dead',
]

# ---------------------------------------------------------------------------
# Optional classes (d6)
#
# Each class overrides parts of the classless build: the dice for HP, silver
# and Omens, fixed modifiers applied to the 3d6 ability roll *before* the
# score table is read, and usually its own weapon/armor dice. `bullets` is
# what the creation wizard shows when the class is highlighted.
# ---------------------------------------------------------------------------
CLASSES = {
    'Fanged deserter': {
        'blurb': 'Disloyal, deranged or simply uncontrollable. Your parliament of teeth has '
                 'always been your ally.',
        'silver_dice': 2, 'omen_die': 2, 'hp_die': 10,
        'ability_mods': {'strength': 2, 'agility': -1, 'presence': -1},
        'weapon_die': 10, 'armor_die': 4,
        'illiterate': True,
        'bullets': [
            'HP: Toughness + d10 — the toughest of the six',
            'Strength +2 on the roll; Agility and Presence −1',
            'Bite attack: DR10, d6 damage, close range. 1–2 on a d6 the enemy gets a free attack',
            'Normal Agility tests are DR14 instead of DR12 (defence excluded)',
            'Illiterate — you cannot use scrolls at all',
            'Starts with 2d6 × 10 silver and d2 Omens',
        ],
        'traits': [
            'Bite attack: DR10 to attack, d6 damage. You must be close to your target. '
            '1–2 on a d6 chance the enemy gets a free attack.',
            'Normal Agility tests are DR14 instead of DR12, excluding defence.',
            'Illiterate; you are incapable of understanding scrolls.',
        ],
        'origin_label': 'Earliest memory',
        'origins': [
            'A burnt-black building in Sarkash. Your home?',
            'A derelict rotting ship rolling endlessly across a grey sea.',
            'A brothel in Schleswig. Quite a friendly environment.',
            'Sleeping with dogs in the corner of an inn, waiting for someone to return.',
            'Following an army in eastern Wästland.',
            'Suckling a wolf in the wild of Bergen Chrypt.',
        ],
        'feature_count': 1,
        'feature_label': 'You also begin with one of the following',
        'features': [
            ('Crumpled monster mask',
             'Strikes primitive fear into lesser creatures like goblins, gnoums and children. '
             'While worn, they check Morale every round.'),
            ('The brown scimitar of Galgenbeck',
             'A stinking sword you pulled from a military shit-ditch. d6 damage. DR10 attack and '
             'defence while you wield it. 1 in 6 chance a wounded enemy is smitten with potent '
             'sepsis, dying in 10 minutes.'),
            ('Wizard teeth',
             'Four weird teeth rattle within a blackened pouch. Before battle roll a d6 for each '
             'one. For every 6, one of your attacks deals maximum damage.'),
            ("Old Sigûrd's sling",
             'Woven from the long grey hair of the strongest man whose throat you ever gnawed. '
             '2d4 damage, requires fist-sized rocks which, perhaps regrettably, are everywhere.'),
            ('Ancient gore-hound',
             'Asthmatic and deluded, but with a superb nose for treasure in the most disgusting '
             'debris. Attacks with DR10 (bite d6). Defends with DR12, 10 HP. Becomes frenzied '
             'around goblins and berserkers.'),
            ("The shoe of Death's horse",
             'In your hands it hits with DR10, d4 damage. 1 in 6 chance the shoe smashes the '
             'skull, instantly killing small-to-medium creatures. It returns to your hand like a '
             'boomerang.'),
        ],
    },

    'Gutterborn Scum': {
        'blurb': 'An ill star smiled upon your birth. A razor blade and a moonless night are '
                 'worth a week of chump-work.',
        'silver_dice': 1, 'omen_die': 2, 'hp_die': 6,
        'ability_mods': {'strength': -2},
        'weapon_die': 6, 'armor_die': 2,
        'bullets': [
            'HP: Toughness + d6',
            'Strength −2 on the roll — you are small',
            'Stealthy: all Presence and Agility tests are DR10 instead of DR12',
            'Weapons rolled on d6, armor on d2 — light and quiet',
            'One specialty from the d6 table (a second one later, when you improve)',
            'Starts with 1d6 × 10 silver and d2 Omens',
        ],
        'traits': [
            'Stealthy: all Presence and Agility tests have their DR reduced by 2 '
            '(normal tests are DR10 instead of DR12).',
            'The first time the Scum gets better, another specialty is rolled.',
        ],
        'origin_label': 'Bad birth',
        'origins': [
            'Dumped onto a moving shit-cart still in your birth caul.',
            'Mother hanged from a tree outside of Galgenbeck, you fell from the corpse.',
            'Raised by rats in the gutters of Grift.',
            "Kicked and beaten beneath a baker's table in Schleswig.",
            'Escaped the Tvelandian orphanarium.',
            'Educated by outlaws in a hovel south of Alliáns.',
        ],
        'feature_count': 1,
        'feature_label': 'You also begin with one specialty',
        'features': [
            ("Coward's jab",
             'When attacking by surprise test Agility DR10. On a success you automatically hit '
             'once with a light one-handed weapon, dealing normal damage +3.'),
            ('Filthy fingersmith',
             'Your snaky little digits get into pockets and pick locks with a DR8 Agility test. '
             'You also begin with lockpicks.'),
            ('Abominable gob lobber',
             'You can spit d2 times during a fight. Roll a DR8 Presence test for accuracy. Targets '
             'are blinded, retching and vomiting for d4 rounds. Anyone witnessing this — friend '
             'and foe — must test Toughness not to also vomit. PCs test DR10, enemies DR12.'),
            ('Escaping fate',
             'Every time you use an Omen there is a 50% chance it is not spent.'),
            ('Excretal stealth',
             'You hide in muck, debris and filth preternaturally well. When hidden in these '
             'conditions a DR16 Presence test is required to notice you.'),
            ('Dodging death',
             'On death, if there is even the slightest possibility that you survived, there is a '
             '50% chance that you did. If so, after 10 rounds you pop back up with d4 HP and an '
             'unlikely explanation.'),
        ],
    },

    'Esoteric hermit': {
        'blurb': 'The stone of your cave is one with the stars. Now the chaos of a fallen world '
                 'disturbs your rituals.',
        'silver_dice': 1, 'omen_die': 4, 'hp_die': 4,
        'ability_mods': {'presence': 2, 'strength': -2},
        'weapon_die': 4, 'armor_die': 2,
        'bonus_scroll': True,
        'bullets': [
            'HP: Toughness + d4 — the frailest of the six',
            'Presence +2 on the roll; Strength −2',
            'd4 Omens instead of d2 — the Fates watch you closely',
            'Begins with one extra random scroll, sacred or unclean',
            'Weapons rolled on d4, armor on d2 — a caster cannot wear plate',
            'Starts with 1d6 × 10 silver',
        ],
        'traits': [
            'Ordinary starting equipment plus one random scroll (sacred or unclean).',
        ],
        'origin_label': 'Eldritch origin',
        'origins': [
            'Awakening, adult, in a ritual circle underneath the northern bridge to Grift.',
            'Wandered, memoryless, from the mouth of a cavern at the cliffs of Terion.',
            'Single child survivor of an incident in the Valley of the Unfortunate Undead.',
            'Dying of plague in a Bergen Chrypt hovel, you touched something from outside.',
            'An average individual until you encountered something in a dim glade in Sarkash.',
            'Raised on a lonely island in Lake Onda. No one else has heard of this island and '
            'you cannot return.',
        ],
        'feature_count': 1,
        'feature_label': 'You also begin with one of the following',
        'features': [
            ('Master of fate',
             'What use are maps when causality itself is open to you? You know the right way with '
             'a DR8 Presence test.'),
            ('Book of boiling blood',
             'Open and read from this book once a day. Your enemy must make a DR12 test to prevent '
             'it. If they fail, d2 Berserker-slayers appear. Roll a d6: on 1–4 they fight '
             'alongside you, on 5–6 they turn on you and try to destroy the book.'),
            ('Speaker of truths',
             'Twice per day, bring clarity to a creature of your choice. The DR of the next test '
             'they undertake is lowered by 4.'),
            ('Initiate of the invisible college',
             'Once per day summon d2 scrolls whose power can be used only once. Roll a d4: on 1–2 '
             'the scrolls are sacred, on 3–4 unclean. Unused, they turn to ash at sunrise.'),
            ('Bard of the undying',
             'You learnt your melodies in the Otherworld. The music of your harp gives +d4 on '
             'reaction rolls.'),
            ('Hawk as weapon',
             'Your crafty almost-intelligent hawk keeps watch, scouts and swoops to attack. '
             'Attacks/defence DR10 (claws/bite d4), HP 8.'),
        ],
    },

    'Wretched Royalty': {
        'blurb': 'Bowed down only by the memories of your own lost glory, you could never submit '
                 'to anyone else. Not you, of noble blood!',
        'silver_dice': 4, 'omen_die': 2, 'hp_die': 6,
        'ability_mods': {},
        'weapon_die': 8, 'armor_die': 4, 'reroll_heavy_armor': True,
        'bullets': [
            'HP: Toughness + d6',
            'Painfully average — no ability adjustments at all',
            'Starts with 4d6 × 10 silver, far and away the richest',
            'Begins with TWO entries from the d6 retinue table, not one',
            'Weapons rolled on d8; armor on d4, rerolling heavy armor',
            'd2 Omens',
        ],
        'traits': [],
        'origin_label': 'Things were going so well, until…',
        'origins': [
            'your Wästland palace was reduced to rubble.',
            'your caravan kingdom of Tveland fell into penury.',
            "King Fathmu IX's brother Zigmund, your father, was murdered.",
            'the southern empire of Südglans sank into the sea.',
            'Anthelia demanded a gift of noble blood.',
            'two young princes were kidnapped west of Bergen Chrypt and disappeared into the '
            'black crevasse of the eastern slopes.',
        ],
        'feature_count': 2,
        'feature_label': 'You begin with two of the following',
        'features': [
            ('The blade of your ancestors',
             'A magnificent, clearly magical talking sword: foppish, unreliable and quietly '
             'contemptuous of you. If continually disappointed it develops a 1 in 6 chance to '
             "'accidentally' attack you or your companions. d6+1 damage, attack/defence DR10."),
            ("'Poltroon' the court jester",
             "Practically useless and an emotional drain, but Poltroon's capering makes enemies "
             'lose focus: for the first two rounds you and your allies get +2 on attack/defence.'),
            ('Barbarister the incredible horse',
             'Magical, intelligent, arrogant, vain, and able to talk. If persuaded to care, he '
             'occasionally adds +2 to Presence tests involving logic and intellect.'),
            ('Hamfund the squire',
             'An intensely cowardly servant who guards the scabbard of the cursed sword Eurekia. '
             'Once per combat, if Ham can be found, Eurekia may be drawn: 2d6 damage, but for '
             'every swing roll a d6 — on a 1 the squire is slain and Eurekia vanishes forever.'),
            ('The snake-skin gift',
             'An expensive sandalwood box bound in snakeskin, containing a silk-wrapped dagger. '
             'd4 damage, but on a 1 the target dies immediately of deadly poison.'),
            ('Horn of the Schleswig lords',
             'Once per day blare this dented old trumpet and test Presence DR12. One creature may '
             'make their next non-combat test an automatic success.'),
        ],
    },

    'Heretical Priest': {
        'blurb': 'Hunted by the Two-Headed Basilisks of the One True Faith, raving in ruins and '
                 'desecrating cathedrals by night.',
        'silver_dice': 3, 'omen_die': 4, 'hp_die': 8,
        'ability_mods': {'presence': 2, 'strength': -2},
        'weapon_die': 8, 'armor_die': 4,
        'bullets': [
            'HP: Toughness + d8',
            'Presence +2 on the roll; Strength −2',
            'd4 Omens instead of d2',
            'May use Powers while wearing medium armor — unique among casters',
            'Weapons rolled on d8',
            'Starts with 3d6 × 10 silver',
        ],
        'traits': [
            'May use Powers while wearing medium armor.',
        ],
        'origin_label': 'Unholy origin',
        'origins': [
            'Galgenbeck, near the cathedral of the Two-Headed Basilisks.',
            'Massacred Alliáns cult, sole survivor.',
            'The crypts of Grift.',
            'Temple ruins in the Valley of the Unfortunate Undead.',
            'One of the many Graven-Tosk thief-tunnels.',
            'Secret Bergen Chrypt church.',
        ],
        'feature_count': 1,
        'feature_label': 'You begin with one of the following',
        'features': [
            ("Sacred shepherd's crook",
             'Its head a hook of human bone inscribed with overlapping anti-prayers. This crook '
             'hooks through other worlds. Staff does 2d4 damage, except to faithless humans.'),
            ('Stolen mitre',
             "While worn, the priest's vile body fades, becoming hard to hit (defence DR10). "
             'Pulled over the ears outside battle, the priest is nearly invisible, testing '
             'stealth against DR8.'),
            ('List of sins',
             'A long, accurate document cross-referenced against reality. Successful Presence '
             'DR10: a strange light surrounds evil creatures, and you defend with +2 against any '
             'being discovered this way.'),
            ('The blasphemous Nechrubel bible',
             'So blasphemous it can only be perused once per day. Roll a die. Even: for the rest '
             'of the day PCs heal d4 HP after five minutes of rest. Odd: the priest is plagued by '
             'd3 demonic hallucinations only they can see, until sunrise.'),
            ("Stones taken from Thel-Emas' lost temple",
             'Cast the stones; their pattern reveals if danger lurks in an adjacent room. The '
             'stones can lie — test Presence DR10 to see if they are true. After a failure you '
             'cannot test again until the sun has set.'),
            ('(Wrong Jesus) Crucifix',
             'Usable in encounters with the undead, lesser trolls and goblins. Check morale '
             "(add or subtract the priest's Presence modifier) to see if the creatures bow and "
             'kindly remove themselves.'),
        ],
    },

    'Occult herbmaster': {
        'blurb': 'Born of the mushroom, raised in the glade, watched by the eye of the moon in a '
                 'silverblack pool.',
        'silver_dice': 2, 'omen_die': 2, 'hp_die': 6,
        'ability_mods': {'toughness': 2, 'strength': -2},
        'weapon_die': 6, 'armor_die': 2,
        'decoctions': True,
        'bullets': [
            'HP: Toughness + d6',
            'Toughness +2 on the roll; Strength −2',
            'Carries a portable laboratory',
            'Brews two random decoctions daily, d4 doses total (they spoil after 24 hours)',
            'Weapons rolled on d6, armor on d2',
            'Starts with 2d6 × 10 silver and d2 Omens',
        ],
        'traits': [
            'You carry a portable laboratory and continually search for frequently expended '
            'ingredients. Daily you have the materials to create two randomly determined '
            'decoctions and can brew a total of d4 doses. Unused, they lose vitality after '
            '24 hours.',
        ],
        'origin_label': 'Probably raised in',
        'origins': [
            'calm isolation in the Sarkash dark.',
            'calm isolation in the Sarkash dark.',
            'calm isolation in the Sarkash dark.',
            'the illegal midnight markets of Schleswig.',
            'the heretic isle of Crëlut, two nautical miles east of Grift.',
            'the old frozen ruins not far from Alliáns.',
            'a little witches cottage in Galgenbeck.',
            "the ruins of the Shadow King's manse, thick with memories of mushrooms and smoke.",
        ],
        'origin_die': 8,
        'feature_count': 0,
        'feature_label': '',
        'features': [],
    },
}

# The herbmaster's daily brews, d8
DECOCTIONS = [
    ('Red poison', 'Toughness DR12 or −d10 HP.'),
    ('Ezumiels vapor', 'Pass a DR14 test or severe (and arguably fun) hallucinations for d4 hours.'),
    ('Southern frog stew', 'Vomit for d4 hours; pass a DR14 test or you can do nothing else.'),
    ('Elixir vitalis', 'Heals d6 HP and stops infection. Can be habit-forming.'),
    ('Spider-owl soup', 'See in darkness and climb on walls for 30 minutes.'),
    ("Fernor's philtre",
     'Translucent oil, dabbed right into the eye. Heals infection and gives +2 on Presence tests '
     'for d4 hours.'),
    ("Hyphos' enervating snuff",
     'Berserk! Two attacks per round but defend with DR14. Lasts one fight. Causes sneezing.'),
    ('Black poison', 'Toughness DR14 or −d6 HP and blinded for one hour.'),
]

CLASSLESS_BULLETS = [
    'HP: Toughness + d8',
    'Roll two abilities with 4d6, drop the lowest die — your choice which two',
    'No ability penalties and no class restrictions',
    'Weapons rolled on d10, armor on d4 — the full tables',
    'Starts with 2d6 × 10 silver and d2 Omens',
]


TRAIT_TABLES = {
    'Terrible Trait': TERRIBLE_TRAITS,
    'Broken Body': BROKEN_BODIES,
    'Bad Habit': BAD_HABITS,
}

# Inventory is split into what a character carries on their person plus any
# number of containers.
#
# On your person: capacity is Strength + 8 and it is impossible to carry more
# than twice that, so 22 slots covers the most anyone could ever hold there
# (Strength +3 -> 2 x 11). Going over capacity is allowed but overloads you.
#
# Containers: each has its own fixed number of slots, ADDED on top of the
# Strength + 8 (a ruling — the book doesn't say either way). A container can
# never be overfilled, and the container itself doesn't use a slot on your
# person. Wagons and donkeys aren't sized by the book; these are defaults the
# DM can change per character.
INVENTORY_SLOTS = 22
CONTAINER_PRESETS = [('Backpack', 7), ('Sack', 10), ('Small wagon', 20), ('Donkey', 15)]
MAX_CONTAINER_SLOTS = 40
MAX_CONTAINERS = 6
MAX_CONTAINER_NAME = 30

# The DM can add a flat +/- modifier to any of their own rolls.
MAX_ROLL_MODIFIER = 20

# Edit protection. Each character keeps a revision number per section of the
# sheet, bumped on every change. Editors send back the revision they loaded;
# if it no longer matches, someone else changed that section in between and
# the save is refused instead of silently overwriting their change.
#   vitals    — hp, max hp, omens, silver (players edit these too)
#   abilities — the four ability scores
#   kit       — weapon, armor
#   inventory — on-person items, free slot, containers and their contents
#   conditions — temporary conditions applied by the DM
REV_SECTIONS = ('vitals', 'abilities', 'kit', 'inventory', 'conditions')

# Temporary conditions. The DM gives each one a name and, optionally, a
# modifier to any of the four abilities. A character's base ability scores are
# never touched: everything that uses an ability (the sheet, stat rolls,
# carrying capacity) uses base + the sum of active conditions, and removing a
# condition simply drops its modifiers again.
MAX_CONDITIONS = 6
MAX_CONDITION_NAME = 30
MAX_CONDITION_MOD = 3
# One extra slot on your person for something nearly weightless (a ring, a
# letter, a lock of hair). It never counts toward Strength + 8.
MAX_ITEM_LENGTH = 60
MAX_SILVER = 999999
MIN_HP = -99
MAX_HP = 999


def carrying_capacity(strength):
    return strength + 8


def condition_mod(character, key):
    return sum(c.get('mods', {}).get(key, 0) for c in character.get('conditions', []))


def effective_ability(character, key):
    """Base ability plus every active condition's modifier to it."""
    return int(character.get(key, 0)) + condition_mod(character, key)


def effective_abilities(character):
    return {key: effective_ability(character, key) for key in ABILITY_KEYS}


def condition_summary(condition):
    """'Strength -1, Toughness +2' — empty when the condition is just a label."""
    return ', '.join(f'{label} {signed(condition["mods"][key])}'
                     for key, label in zip(ABILITY_KEYS, ABILITIES)
                     if condition.get('mods', {}).get(key))


def public_conditions(character):
    return [{'id': c['id'], 'name': c['name'], 'summary': condition_summary(c)}
            for c in character.get('conditions', [])]


def bump(character, *sections):
    revs = character.setdefault('revs', {})
    for section in sections:
        revs[section] = revs.get(section, 0) + 1


def rev_matches(character, section, submitted):
    """True if `submitted` (from a form string or JSON int) is the
    section's current revision."""
    try:
        return int(submitted) == character.get('revs', {}).get(section, 0)
    except (TypeError, ValueError):
        return False


def sheet_state(character):
    """What a player's open board needs to notice DM changes."""
    return {
        'revs': character.get('revs', {}),
        'hp': character.get('hp', 0),
        'max_hp': character.get('max_hp', 0),
        'omens': character.get('omens', 0),
        'silver': character.get('silver', 0),
        'dead': bool(character.get('dead')),
        'abilities': effective_abilities(character),
        'base_abilities': {key: character.get(key, 0) for key in ABILITY_KEYS},
        'capacity': carrying_capacity(effective_ability(character, 'strength')),
        'conditions': public_conditions(character),
    }


def roster_row(character):
    """One line of the DM's Players roster."""
    inventory = character.get('inventory', [])
    return {
        'id': character['id'],
        'name': character['name'],
        'color': character.get('color', ''),
        'class_name': character.get('class_name', ''),
        'hp': character.get('hp', 0),
        'max_hp': character.get('max_hp', 0),
        'omens': character.get('omens', 0),
        'carried': sum(1 for item in inventory if item.strip()),
        'capacity': carrying_capacity(effective_ability(character, 'strength')),
        'conditions': [c['name'] for c in character.get('conditions', [])],
        'stored': sum(1 for c in character.get('containers', []) for item in c['items'] if item.strip()),
        'storage': sum(c['capacity'] for c in character.get('containers', [])),
        'dead': bool(character.get('dead')),
        'revs': character.get('revs', {}),
    }


def new_container(name, capacity):
    capacity = max(1, min(MAX_CONTAINER_SLOTS, int(capacity)))
    return {'id': secrets.token_hex(4), 'name': name, 'capacity': capacity,
            'items': [''] * capacity}


def container_from_text(text):
    """Turn a container description — a CONTAINERS table entry such as
    'Sack (holds 10 normal-sized items)', or whatever the DM once typed into
    the old free-text 'Carried in' field — into a container, or None for
    'Nothing'."""
    text = (text or '').strip()
    if not text or text.lower() == 'nothing':
        return None
    held = re.search(r'holds\s+(\d+)', text, re.IGNORECASE)
    for name, capacity in CONTAINER_PRESETS:
        if text.lower().startswith(name.lower()):
            return new_container(name, int(held.group(1)) if held else capacity)
    name = re.sub(r'\s*\(.*\)\s*$', '', text).strip()[:MAX_CONTAINER_NAME] or 'Container'
    return new_container(name, int(held.group(1)) if held else 10)


def fit_items(items, size):
    """Clean a submitted slot list and pad/trim it to exactly `size`."""
    cleaned = [clean_text(i if isinstance(i, str) else '', MAX_ITEM_LENGTH) for i in (items or [])[:size]]
    return cleaned + [''] * (size - len(cleaned))


def inventory_changes(character, new_person, new_containers, new_free):
    """Human-readable diff of an inventory save, for the activity log.
    new_containers maps container id -> new item list."""
    changes = []
    if character.get('free_item', '') != new_free:
        changes.append(f'free: "{character.get("free_item", "")}" -> "{new_free}"')
    old_person = character.get('inventory', [''] * INVENTORY_SLOTS)
    changes += [f'person {i + 1}: "{old_person[i]}" -> "{new_person[i]}"'
                for i in range(INVENTORY_SLOTS) if old_person[i] != new_person[i]]
    for c in character.get('containers', []):
        new_items = new_containers.get(c['id'])
        if new_items is None:
            continue
        changes += [f'{c["name"]} {i + 1}: "{c["items"][i]}" -> "{new_items[i]}"'
                    for i in range(c['capacity']) if c['items'][i] != new_items[i]]
    return changes


def presence_count(presence, bonus, minimum=1):
    """Several starting items are quantified as 'Presence + N'. A negative
    Presence can drive that to zero or below, so floor it at `minimum`."""
    return max(minimum, presence + bonus)


def gear_table_one(n, presence):
    """d12 equipment table. Presence-scaled counts are resolved at creation
    time so the player gets a concrete number in their inventory."""
    return {
        1: 'Rope, 30 feet',
        2: f'Torches x{presence_count(presence, 4)}',
        3: f'Lantern (oil for {presence_count(presence, 6)} hours)',
        4: 'Magnesium strip',
        5: f'Unclean scroll: {random.choice(UNCLEAN_SCROLLS)}',
        6: 'Sharp needle',
        7: f'Medicine chest ({presence_count(presence, 4)} uses)',
        8: 'Metal file and lockpicks',
        9: 'Bear trap (Presence DR14 to spot, d8 damage)',
        10: 'Bomb (sealed bottle, d10 damage)',
        11: 'Red poison, d4 doses (Toughness DR12 or d10 damage)',
        12: 'Silver crucifix',
    }[n]


def gear_table_two(n):
    return {
        1: 'Life elixir, d4 doses (heals d6 HP, removes infection)',
        2: f'Sacred scroll: {random.choice(SACRED_SCROLLS)}',
        3: 'Small vicious dog (d6+2 HP, bite d4, obeys only you)',
        4: f'{roll_dn(4)} monkeys that ignore but love you (d4+2 HP, punch/bite d4)',
        5: 'Exquisite perfume (worth 25s)',
        6: 'Toolbox (10 nails, tongs, hammer, small saw, drill)',
        7: 'Heavy chain, 15 feet',
        8: 'Grappling hook',
        9: 'Shield (-1 damage, or break it to ignore one attack)',
        10: 'Crowbar (d4 damage)',
        11: 'Lard (5 meals in a pinch)',
        12: 'Tent',
    }[n]


# ---------------------------------------------------------------------------
# Persistence — files living next to app.py
# ---------------------------------------------------------------------------
BASE_DIR = os.path.dirname(os.path.abspath(__file__))

# Game state normally sits next to app.py. In a container that directory holds
# the code, so a volume mounted over it would hide the app — MORKBORG_DATA_DIR
# points the four state files somewhere separate instead.
DATA_DIR = os.environ.get('MORKBORG_DATA_DIR') or BASE_DIR
os.makedirs(DATA_DIR, exist_ok=True)

# Prove the directory is writable before anything else happens. Without this
# a misconfigured volume looks fine until the first save, and the difference
# between "saving correctly" and "saving into a container layer that vanishes
# on restart" is invisible until the data is already gone.
try:
    _probe = os.path.join(DATA_DIR, '.write-test')
    with open(_probe, 'w', encoding='utf-8') as _f:
        _f.write('')
    os.remove(_probe)
except OSError as _exc:
    raise SystemExit(
        f'\nCannot write to the data directory: {DATA_DIR}\n'
        f'  {_exc}\n\n'
        'Game state would be lost. Fix the permissions on that directory, or\n'
        'point MORKBORG_DATA_DIR somewhere writable, then start again.\n'
    )

print(f'[morkborg] game state directory: {DATA_DIR}', flush=True)

DATA_FILE = os.path.join(DATA_DIR, 'Hidden Message Board.json')
CHAR_FILE = os.path.join(DATA_DIR, 'Characters.json')
LOG_FILE = os.path.join(DATA_DIR, 'Activity Log.txt')
SCENE_FILE = os.path.join(DATA_DIR, 'Scene.json')

# The rules markdown. Any of these filenames works, so you can keep the file
# exactly as downloaded (umlaut and all) or rename it to something your
# filesystem is happier with.
RULES_FILENAMES = [
    'MÖRK_BORG_BARE_BONES_EDITION.md',
    'MORK_BORG_BARE_BONES_EDITION.md',
    'MÖRK BORG BARE BONES EDITION.md',
    'rules.md',
]
RULES_TITLE = 'MÖRK BORG — Bare Bones Edition'

# Drop adventure files (.html or .md) in here and they appear as pop-out
# buttons on the DM dashboard automatically.
ADVENTURE_DIR = os.environ.get('MORKBORG_ADVENTURE_DIR') or os.path.join(BASE_DIR, 'adventures')

# Adventures that get a button whether or not the file exists yet. Anything
# else found in ADVENTURE_DIR is listed after these.
KNOWN_ADVENTURES = [
    {'slug': 'rotblack-sludge', 'title': 'Rotblack Sludge',
     'filenames': ['rotblack-sludge.html', 'rotblack-sludge.md',
                   'Rotblack Sludge.html', 'Rotblack Sludge.md']},
    {'slug': 'two-guillians', 'title': 'Two Guillians',
     'filenames': ['two-guillians.html', 'two-guillians.md',
                   'two-guillians-print.html', 'Two Guillians.html']},
    {'slug': 'path-of-the-penitent.html', 'title': 'Path of the Penitent',
     'filenames': ['path-of-the-penitent.html', 'path-of-the-penitent.md',
                   'path-of-the-penitent.html', 'Path of the Penitent.html']},
]

DEFAULT_SCENE_NAME = 'The Dying World'
MAX_SCENE_LENGTH = 60

# Private notes: one page per character, plus one for the DM. Only the owner
# can read or write theirs. Character notes live on the character in
# Characters.json; the DM's live in their own file.
MAX_NOTES_LENGTH = 500
DM_NOTES_FILE = os.path.join(DATA_DIR, 'DMNotes.json')

# Append-only audit trail of every player and DM change. Uses the logging
# module (not a manual open()/write()) because FileHandler is thread-safe —
# the dev server runs with threaded=True, so concurrent requests could
# otherwise interleave or clobber each other's writes to the same file.
activity_logger = logging.getLogger('activity')
activity_logger.setLevel(logging.INFO)
activity_logger.propagate = False  # don't also spam Flask's own console logger
if not activity_logger.handlers:
    _handler = logging.FileHandler(LOG_FILE, encoding='utf-8')
    _handler.setFormatter(logging.Formatter('%(asctime)s | %(message)s', datefmt='%Y-%m-%d %H:%M:%S'))
    activity_logger.addHandler(_handler)


def log_activity(actor, action, details=''):
    msg = f'{actor} | {action}'
    if details:
        msg += f' | {details}'
    activity_logger.info(msg)


def load_json_file(path):
    if not os.path.exists(path):
        return {}
    try:
        with open(path, 'r', encoding='utf-8') as f:
            return json.load(f)
    except (json.JSONDecodeError, OSError):
        return {}


def load_scene_name():
    data = load_json_file(SCENE_FILE)
    name = data.get('scene_name', '').strip() if isinstance(data, dict) else ''
    return name or DEFAULT_SCENE_NAME


def save_scene_name(name):
    with open(SCENE_FILE, 'w', encoding='utf-8') as f:
        json.dump({'scene_name': name}, f, indent=2)


def load_dm_notes():
    data = load_json_file(DM_NOTES_FILE)
    notes = data.get('notes', '') if isinstance(data, dict) else ''
    return notes if isinstance(notes, str) else ''


def save_dm_notes(notes):
    with open(DM_NOTES_FILE, 'w', encoding='utf-8') as f:
        json.dump({'notes': notes}, f, indent=2)


def clean_notes(value):
    """Like clean_text(), but notes are multi-line: newlines are kept
    (normalised to \\n), tabs become spaces, and every other control or
    non-printable character is dropped. Length is checked by the caller so
    an over-long note is refused rather than silently cut."""
    value = value.replace('\r\n', '\n').replace('\r', '\n').replace('\t', ' ')
    value = ''.join(ch for ch in value if ch in '\n ' or ch.isprintable())
    return value.rstrip()


def load_posts():
    if not os.path.exists(DATA_FILE):
        return []
    try:
        with open(DATA_FILE, 'r', encoding='utf-8') as f:
            data = json.load(f)
    except (json.JSONDecodeError, OSError):
        return []

    # Same defensive defaults as load_character_store: this file is plain JSON
    # next to the script, and a hand-edited post missing a field shouldn't be
    # able to break the feed.
    for i, p in enumerate(data):
        p.setdefault('id', str(uuid.uuid4()))
        p.setdefault('is_dm', False)
        p.setdefault('color', PLAYER_COLORS[0])
        p.setdefault('is_private', False)
        p.setdefault('target_character_id', None)
        p.setdefault('target_character_name', '')
        p.setdefault('to_dm', False)
        p.setdefault('author_character_id', None)
        p.setdefault('edited', False)
        p.setdefault('change', 0)
        p.setdefault('seq', i)  # stable ordering key for the live-feed poller
    return data


def save_posts():
    with open(DATA_FILE, 'w', encoding='utf-8') as f:
        json.dump(posts, f, indent=2)


def save_characters():
    with open(CHAR_FILE, 'w', encoding='utf-8') as f:
        json.dump({'characters': characters, 'client_map': client_map}, f, indent=2)


def generate_username(taken):
    """A random 'grim-word' username, e.g. rotten-crow-42. `taken` is a set
    of lowercased usernames already in use."""
    while True:
        name = (f'{secrets.choice(USERNAME_WORDS_A)}-{secrets.choice(USERNAME_WORDS_B)}'
                f'-{secrets.randbelow(90) + 10}')
        if name not in taken:
            return name


def generate_password():
    return ''.join(secrets.choice(PASSWORD_ALPHABET) for _ in range(PASSWORD_LENGTH))


def taken_usernames(chars):
    return {c['username'].lower() for c in chars.values() if c.get('username')}


def roll_dn(n):
    return random.randint(1, n)


def roll_xdy(x, y):
    return [random.randint(1, y) for _ in range(x)]


def assign_character_color(existing_characters):
    """Pick the least-used palette color (random among ties) so the first
    len(PLAYER_COLORS) characters are all guaranteed distinct, and colors
    only start repeating once the party outgrows the palette."""
    used = [c.get('color') for c in existing_characters.values() if c.get('color')]
    counts = {color: used.count(color) for color in PLAYER_COLORS}
    min_count = min(counts.values())
    candidates = [color for color, n in counts.items() if n == min_count]
    return random.choice(candidates)


def load_character_store():
    """Returns (characters, client_map).

    characters: character_id -> character dict (persists forever, even after
                a player retires/replaces it, so the DM keeps a full record)
    client_map: LEGACY. client_id -> character_id, from when characters were
                tied to a browser cookie instead of a login. Kept only so a
                browser that was attached before the switch is signed in
                automatically on its next visit (see get_character()); each
                entry is consumed the first time it is used.

    Missing fields are filled in with safe defaults on the way through. Nothing
    written by this app should ever be missing them, but the file is plain JSON
    sitting next to the script and is easy to hand-edit, so a typo there
    shouldn't take the board down.
    """
    raw = load_json_file(CHAR_FILE)

    if isinstance(raw, dict) and 'characters' in raw and 'client_map' in raw:
        chars = raw['characters']
        cmap = raw['client_map']
    else:
        chars = {}
        cmap = {}

    changed = False

    # Drop legacy browser links that point at characters no longer on file.
    for cid in [cid for cid, chid in cmap.items() if chid not in chars]:
        del cmap[cid]
        changed = True

    taken = taken_usernames(chars)
    for char_id, char in chars.items():
        char.setdefault('id', char_id)

        # Retroactive login migration: every character that predates the
        # username/password system (i.e. anything that had a claim link) gets
        # credentials generated here, once, and written back below.
        if not char.get('username'):
            char['username'] = generate_username(taken)
            taken.add(char['username'].lower())
            changed = True
        if not char.get('password'):
            char['password'] = generate_password()
            changed = True
        if 'login_version' not in char:
            char['login_version'] = 1
            changed = True
        revs = char.setdefault('revs', {})
        for section in REV_SECTIONS:
            if section not in revs:
                revs[section] = 0
                changed = True
        if 'client_id' in char:
            del char['client_id']
            changed = True

        char.setdefault('dead', False)
        if 'color' not in char:
            char['color'] = assign_character_color(chars)
            changed = True

        for key in ABILITY_KEYS:
            if key not in char:
                char[key] = 0
                changed = True
        for key, default in (('hp', 1), ('max_hp', 1), ('silver', 0), ('omens', 1),
                             ('armor_tier', 0), ('food', 0)):
            if key not in char:
                char[key] = default
                changed = True
        for key, default in (('weapon', 'Unarmed (d2)'), ('armor', ARMOR[0][0]),
                             ('class_name', ''), ('origin', ''), ('free_item', ''), ('notes', ''),
                             ('conditions', [])):
            if key not in char:
                char[key] = default
                changed = True
        if 'traits' not in char:
            char['traits'] = {}
            changed = True
        for key in ('features', 'class_traits'):
            if key not in char:
                char[key] = []
                changed = True

        inventory = char.get('inventory') or []
        if len(inventory) != INVENTORY_SLOTS:
            inventory = [str(i or '') for i in inventory][:INVENTORY_SLOTS]
            inventory += [''] * (INVENTORY_SLOTS - len(inventory))
            char['inventory'] = inventory
            changed = True

        # One-time move from the old free-text 'container' field to real
        # containers. The old creation code also put the container into the
        # inventory as an item; that slot is cleared since the container now
        # has its own box and no longer takes up room on your person.
        if 'containers' not in char:
            old = char.pop('container', '')
            container = container_from_text(old)
            char['containers'] = [container] if container else []
            if container:
                for i, item in enumerate(char['inventory']):
                    if item.strip().lower() == old.strip().lower():
                        char['inventory'][i] = ''
                        break
            changed = True
        for c in char['containers']:
            if len(c.get('items', [])) != c.get('capacity', 0):
                c['items'] = fit_items(c.get('items'), c['capacity'])
                changed = True

    if changed:
        # Write the filled-in defaults back so this only has to happen once
        with open(CHAR_FILE, 'w', encoding='utf-8') as f:
            json.dump({'characters': chars, 'client_map': cmap}, f, indent=2)

    return chars, cmap


posts = load_posts()
characters, client_map = load_character_store()  # see load_character_store() docstring
scene_name = load_scene_name()
dm_notes = load_dm_notes()
_next_post_seq = (max((p.get('seq', -1) for p in posts), default=-1)) + 1


# Edits and deletions after a post has been shown. Every edit stamps the post
# with a new value of this counter, and every deletion is remembered here, so
# a poller that sends the last value it saw (after_change) gets back exactly
# what changed since. Deletions are only kept in memory: after a restart a
# deleted post can linger in an already-open tab until it's reloaded.
_feed_change = max((p.get('change', 0) for p in posts), default=0)
_recent_deletions = []  # (change, post_id), newest last
MAX_RECENT_DELETIONS = 500


def next_feed_change():
    global _feed_change
    _feed_change += 1
    return _feed_change


def record_post_deletion(post_id):
    _recent_deletions.append((next_feed_change(), post_id))
    del _recent_deletions[:-MAX_RECENT_DELETIONS]


def post_created_at(post):
    """Epoch seconds the post was made. Older posts only have the display
    timestamp, so fall back to parsing that."""
    if isinstance(post.get('created_at'), (int, float)):
        return post['created_at']
    try:
        return datetime.strptime(post.get('timestamp', ''), '%Y-%m-%d %H:%M:%S').timestamp()
    except ValueError:
        return 0


def own_post_permissions(post, character):
    """(seconds left to edit, may delete) for `character` on `post`;
    (0, False) when it isn't theirs or the window has closed."""
    if (not character or post.get('is_dm') or character.get('dead')
            or post.get('author_character_id') != character['id']):
        return 0, False
    left = int(post_created_at(post) + POST_EDIT_WINDOW_SECONDS - datetime.now().timestamp())
    if left <= 0:
        return 0, False
    return left, not post.get('rolls')


def next_post_seq():
    global _next_post_seq
    seq = _next_post_seq
    _next_post_seq += 1
    return seq


@app.context_processor
def inject_scene_name():
    # Makes {{ scene_name }} available in every template render_cached() renders
    # (TOP_BAR's <h1> and the board's <title>) without threading it through
    # every route's context kwargs.
    return {'scene_name': scene_name}


def log_in_as(character):
    """Bind this browser's session to a character. login_version is copied in
    so that a DM password reset (which bumps it) signs out every browser that
    logged in with the old password."""
    session.pop('client_id', None)
    session['character_id'] = character['id']
    session['login_version'] = character.get('login_version', 1)
    session.permanent = True


def log_out_player():
    session.pop('character_id', None)
    session.pop('login_version', None)


def get_character():
    char_id = session.get('character_id')
    if char_id:
        character = characters.get(char_id)
        if character and session.get('login_version') == character.get('login_version', 1):
            return character
        # Character deleted, or its password was reset since this login.
        log_out_player()
        return None

    # One-time upgrade for a browser that was attached to a character under
    # the old cookie-only system: sign it straight in and retire the link.
    legacy_id = session.get('client_id')
    if legacy_id and legacy_id in client_map:
        character = characters.get(client_map.pop(legacy_id))
        save_characters()
        if character:
            log_in_as(character)
            log_activity(character['name'], 'LEGACY_BROWSER_LINK_CONVERTED')
            flash(f"This browser link has been converted to a login. Your username is "
                  f"{character['username']} and your password is {character['password']} "
                  f"(also shown at the bottom of your character sheet).")
            return character
    return None


def find_character_by_username(username):
    wanted = username.strip().lower()
    if not wanted:
        return None
    for character in characters.values():
        if character.get('username', '').lower() == wanted:
            return character
    return None


# ip -> list of datetimes of recent failed player logins (in memory only)
_login_failures = {}


def login_throttled(ip):
    cutoff = datetime.now() - LOGIN_FAILURE_WINDOW
    recent = [t for t in _login_failures.get(ip, []) if t > cutoff]
    if recent:
        _login_failures[ip] = recent
    else:
        _login_failures.pop(ip, None)
    return len(recent) >= LOGIN_MAX_FAILURES


def clean_text(value, max_len):
    value = value.strip()
    value = ''.join(ch for ch in value if ch == ' ' or (ch.isprintable() and ch not in '\r\n\t'))
    return value[:max_len]


def signed(n):
    """MÖRK BORG abilities are modifiers, so they always carry a sign."""
    return f'+{n}' if n >= 0 else str(n)


app.jinja_env.filters['signed'] = signed


# ---------------------------------------------------------------------------
# Minimal Markdown -> HTML renderer
#
# Just enough Markdown to render the Bare Bones rules (headings, GFM tables,
# bullet lists, bold/italic, paragraphs) without pulling in a dependency —
# this runs on a Pi and `pip install markdown` is one more thing to go wrong.
#
# The source file is trusted (it sits next to app.py, put there by you), and
# it contains deliberate inline HTML — <u> and <br> that survived the PDF
# text extraction — so its content is passed through rather than escaped.
# Don't point RULES_FILENAMES at anything you didn't write or download
# yourself.
# ---------------------------------------------------------------------------
_MD_TABLE_SEP_RE = re.compile(r'^\|[\s:|-]+\|$')
# Matches both bullets and numbered items, capturing the indent so nested
# lists can be rebuilt: "  3. Reach up through the fire" -> ('  ', '3.', ...)
_MD_LIST_RE = re.compile(r'^(\s*)([-*]|\d+[.)])\s+(.*)$')
_MD_QUOTE_RE = re.compile(r'^>\s?(.*)$')
_MD_HEADING_RE = re.compile(r'^(#{1,6})\s+(.*)$')

# The OCR'd rules carry a running footer ("MÖRK BORG BARE BONES EDITION"
# followed by a page number on its own line) and blocks of garbled text
# scraped out of the page artwork. Both are noise in a scrolling web view.
_MD_RUNNING_FOOTER = 'MÖRK BORG BARE BONES EDITION'
_MD_PICTURE_RE = re.compile(r'<!--\s*Start of picture text\s*-->.*?<!--\s*End of picture text\s*-->',
                            re.DOTALL | re.IGNORECASE)
_MD_COMMENT_RE = re.compile(r'<!--.*?-->', re.DOTALL)


def _md_inline(text):
    text = re.sub(r'\*\*(.+?)\*\*', r'<strong>\1</strong>', text)
    text = re.sub(r'(?<!\*)\*(?!\*)(.+?)(?<!\*)\*(?!\*)', r'<em>\1</em>', text)
    text = re.sub(r'(?<![\w\\])_([^_\n]+?)_(?![\w])', r'<em>\1</em>', text)
    return text


# "1", "1-2", "1–3", "11–16" — a die result rather than a column label
_MD_RESULT_CELL_RE = re.compile(r'^\d+\s*[–—-]?\s*\d*$')
_MD_TAG_RE = re.compile(r'<[^>]+>')


def _md_strip_tags(cell):
    return _MD_TAG_RE.sub('', cell).strip()


def _md_split_row(line):
    return [_md_inline(cell.strip()) for cell in line.strip().strip('|').split('|')]


def _md_parse_list(lines, i, base_indent):
    """Parse one list block starting at lines[i], returning (html, next_i).

    Handles three things the rules text actually uses: numbered lists that
    don't start at 1 (a d20 table split across a page break resumes at 20),
    lists nested under an item by indentation, and unindexed continuation
    lines that belong to the item above them (a creature's stat line written
    under its entry).
    """
    n = len(lines)
    items = []           # each item: {'text': [...], 'subs': [html, ...]}
    ordered = None
    start = 1

    while i < n:
        raw = lines[i]
        if not raw.strip():
            break

        m = _MD_LIST_RE.match(raw)
        if m:
            indent = len(m.group(1).expandtabs(4))
            if indent < base_indent:
                break
            if indent > base_indent:
                if not items:
                    break
                sub_html, i = _md_parse_list(lines, i, indent)
                items[-1]['subs'].append(sub_html)
                continue

            marker = m.group(2)
            is_ordered = marker[0].isdigit()
            if ordered is None:
                ordered = is_ordered
                if is_ordered:
                    start = int(marker[:-1])
            elif is_ordered != ordered:
                break  # a bullet list butting up against a numbered one

            items.append({'text': [m.group(3).strip()], 'subs': []})
            i += 1
            continue

        # Not a list marker: an indented line continues the previous item.
        indent = len(raw) - len(raw.lstrip())
        if items and indent > base_indent:
            items[-1]['text'].append(raw.strip())
            i += 1
            continue
        break

    if not items:
        return '', i

    parts = []
    for item in items:
        parts.append('<li>' + _md_inline(' '.join(item['text'])) + ''.join(item['subs']) + '</li>')

    if ordered:
        attr = f' start="{start}"' if start != 1 else ''
        return f'<ol{attr}>' + ''.join(parts) + '</ol>', i
    return '<ul>' + ''.join(parts) + '</ul>', i


def md_to_html(text):
    text = _MD_PICTURE_RE.sub('', text)
    text = _MD_COMMENT_RE.sub('', text)

    lines = text.split('\n')
    out = []
    quote = []
    para = []
    i = 0
    n = len(lines)

    def flush_para():
        if para:
            out.append('<p>' + _md_inline(' '.join(para)) + '</p>')
            para.clear()

    def flush_quote():
        if quote:
            out.append('<blockquote>' + _md_inline(' '.join(quote)) + '</blockquote>')
            quote.clear()

    def flush_bullets():
        flush_quote()

    while i < n:
        raw = lines[i]
        line = raw.strip()

        # Drop the running footer and the bare page number that follows it
        if line == _MD_RUNNING_FOOTER:
            flush_para()
            flush_bullets()
            i += 1
            while i < n and not lines[i].strip():
                i += 1
            if i < n and lines[i].strip().isdigit():
                i += 1
            continue

        if not line:
            flush_para()
            flush_bullets()
            i += 1
            continue

        # Table: a pipe row whose *next* line is the |---|---| separator
        if line.startswith('|') and i + 1 < n and _MD_TABLE_SEP_RE.match(lines[i + 1].strip()):
            flush_para()
            flush_bullets()
            header = _md_split_row(line)
            i += 2
            body = []
            while i < n and lines[i].strip().startswith('|'):
                body.append(_md_split_row(lines[i].strip()))
                i += 1
            # Many tables in the rules have no real header — the first row is
            # already a result ("|1-2|nothing|"). GFM would render that as a
            # header cell, which reads as though "1-2" labels the column, so
            # a numeric first cell demotes the whole row back into the body.
            if _MD_RESULT_CELL_RE.match(_md_strip_tags(header[0])):
                body.insert(0, header)
                header = None
            html = ['<table>']
            if header:
                html.append('<thead><tr>' + ''.join(f'<th>{c}</th>' for c in header) + '</tr></thead>')
            html.append('<tbody>')
            for row in body:
                html.append('<tr>' + ''.join(f'<td>{c}</td>' for c in row) + '</tr>')
            html.append('</tbody></table>')
            out.append(''.join(html))
            continue

        # A pipe row with no separator line — render it as a plain row anyway
        if line.startswith('|') and line.endswith('|'):
            flush_para()
            flush_bullets()
            cells = _md_split_row(line)
            out.append('<table><tbody><tr>' +
                       ''.join(f'<td>{c}</td>' for c in cells) +
                       '</tr></tbody></table>')
            i += 1
            continue

        heading = _MD_HEADING_RE.match(line)
        if heading:
            flush_para()
            flush_bullets()
            level = min(6, len(heading.group(1)))
            body = _md_inline(heading.group(2).strip())
            if body:
                out.append(f'<h{level}>{body}</h{level}>')
            i += 1
            continue

        # A horizontal rule has to be tested before the list matcher, or the
        # "---" separators in this file each become an empty bullet.
        if set(line) <= set('-_=*') and len(line) >= 3:
            flush_para()
            flush_bullets()
            out.append('<hr>')
            i += 1
            continue

        if _MD_LIST_RE.match(raw):
            flush_para()
            flush_quote()
            indent = len(_MD_LIST_RE.match(raw).group(1).expandtabs(4))
            html, i = _md_parse_list(lines, i, indent)
            if html:
                out.append(html)
                continue
            i += 1  # malformed — don't spin on the same line
            continue

        quoted = _MD_QUOTE_RE.match(line)
        if quoted:
            flush_para()
            quote.append(quoted.group(1).strip())
            i += 1
            continue

        flush_bullets()
        para.append(line)
        i += 1

    flush_para()
    flush_bullets()
    return '\n'.join(out)


def find_file(directory, filenames):
    """Return the first of `filenames` that exists in `directory`.

    Filenames are compared after Unicode NFC/NFD normalisation because macOS
    stores 'Ö' decomposed while Linux stores it composed — without this, a
    file copied between the two silently stops being found.
    """
    if not os.path.isdir(directory):
        return None
    try:
        present = os.listdir(directory)
    except OSError:
        return None
    normalised = {unicodedata.normalize('NFC', name): name for name in present}
    for wanted in filenames:
        actual = normalised.get(unicodedata.normalize('NFC', wanted))
        if actual:
            return os.path.join(directory, actual)
    return None


def read_text_file(path):
    try:
        with open(path, 'r', encoding='utf-8') as f:
            return f.read()
    except (OSError, UnicodeDecodeError):
        return None


# The rendered rules are cached after the first request: converting 60KB of
# Markdown on every pop-out open is wasted work on a Pi, and the file doesn't
# change while the server is running.
_rules_cache = None


def get_rules_html():
    global _rules_cache
    if _rules_cache is not None:
        return _rules_cache
    path = find_file(BASE_DIR, RULES_FILENAMES)
    if not path:
        _rules_cache = None
        return None
    text = read_text_file(path)
    if text is None:
        _rules_cache = None
        return None
    html = md_to_html(text)
    # The file opens with its own title heading, but the rules page already
    # prints a masthead above it — drop the duplicate.
    html = re.sub(r'^\s*<h1>.*?</h1>\s*(<hr>)?\s*', '', html, count=1)
    _rules_cache = html
    return _rules_cache


def list_adventures():
    """Every adventure that gets a pop-out button on the DM dashboard.

    KNOWN_ADVENTURES always appear (with `available: False` if the file isn't
    there yet, so Rotblack Sludge can sit as a placeholder until you drop it
    in). Anything else in ADVENTURE_DIR is picked up automatically — no code
    change needed to add the next one.
    """
    found = []
    claimed = set()

    for entry in KNOWN_ADVENTURES:
        path = find_file(ADVENTURE_DIR, entry['filenames'])
        if path:
            claimed.add(os.path.basename(path))
        found.append({
            'slug': entry['slug'],
            'title': entry['title'],
            'path': path,
            'available': path is not None,
        })

    if os.path.isdir(ADVENTURE_DIR):
        try:
            extras = sorted(os.listdir(ADVENTURE_DIR))
        except OSError:
            extras = []
        for name in extras:
            if name in claimed or name.startswith('.'):
                continue
            stem, ext = os.path.splitext(name)
            if ext.lower() not in ('.html', '.htm', '.md', '.markdown'):
                continue
            found.append({
                'slug': slugify(stem),
                'title': stem.replace('-', ' ').replace('_', ' ').strip().title(),
                'path': os.path.join(ADVENTURE_DIR, name),
                'available': True,
            })

    return found


def slugify(value):
    value = unicodedata.normalize('NFKD', value).encode('ascii', 'ignore').decode('ascii')
    value = re.sub(r'[^a-zA-Z0-9]+', '-', value).strip('-').lower()
    return value or 'adventure'


def find_adventure(slug):
    for entry in list_adventures():
        if entry['slug'] == slug:
            return entry
    return None


_SCRIPT_RE = re.compile(r'<script\b.*?</script>', re.DOTALL | re.IGNORECASE)


def strip_scripts(html):
    """Adventure HTML is served inside your own app's origin, so anything it
    contains runs with access to the session cookie. Files exported from a
    browser or a managed machine can carry injected analytics/monitoring
    scripts you didn't put there, so <script> blocks are stripped on the way
    out. Layout and styling are untouched."""
    return _SCRIPT_RE.sub('', html)


_BOLD_RE = re.compile(r'\*([^\n*]+?)\*')
_ITALIC_QUOTE_RE = re.compile(r'"([^\n"]+?)"')


def format_message(message):
    """Jinja filter: turns a raw post message into safe HTML with
    *asterisks* -> bold, "quotes" -> italicized dialogue (quotes kept), and
    @Character mentions highlighted in that character's own color.

    Order matters: the message is HTML-escaped first (with quote=False,
    since this is rendered as element content, never an attribute value, so
    literal " and ' need no encoding and stay usable as markup below).
    Bold/italic run before mentions so the mention span's own markup can't
    be re-matched by the quote/asterisk passes that follow it.
    """
    text = escape(message, quote=False)

    text = _BOLD_RE.sub(r'<strong>\1</strong>', text)
    text = _ITALIC_QUOTE_RE.sub(r'<em>"\1"</em>', text)

    # Longest name first so a shorter character's name can't swallow part of
    # a longer one that starts with it (e.g. "Gri" vs "Grix").
    color_by_name = {
        c['name'].lower(): c.get('color', PLAYER_COLORS[0])
        for c in characters.values() if c.get('name')
    }
    names = sorted(color_by_name.keys(), key=len, reverse=True)
    for name_lower in names:
        esc_name = escape(name_lower, quote=False)
        if not esc_name:
            continue
        color = escape(color_by_name[name_lower], quote=True)
        pattern = re.compile(r'@' + re.escape(esc_name) + r'(?!\w)', re.IGNORECASE)
        text = pattern.sub(
            lambda m, color=color: f"<span class='mention' style='color:{color}; border:1px solid {color};'>{m.group(0)}</span>",
            text
        )

    return text


app.jinja_env.filters['format_message'] = format_message


def parse_submitted_rolls(rolls_raw, character=None, allow_modifier=False):
    """Validate/clean a client-submitted 'rolls' JSON payload (used by both
    player posts and DM posts, since both use the same dice-roller widget).
    Every die value is re-checked against DICE_TYPES bounds server-side —
    the client's totals are never trusted as-is.

    When a player's roll names an ability ('agility', 'presence', ...), that
    ability's modifier is read from `character` here and added to the total,
    so the stat applied is always the one on file, not whatever the browser
    sent. DM rolls pass no character, so any ability field is ignored.

    DM rolls pass allow_modifier=True instead, which accepts a whole-number
    'modifier' (within +/-MAX_ROLL_MODIFIER) on each roll. A modifier of 0
    adds nothing to the description, so unmodified rolls read as before."""
    clean_rolls = []
    try:
        submitted_rolls = json.loads(rolls_raw)
    except (json.JSONDecodeError, TypeError):
        submitted_rolls = []

    if not isinstance(submitted_rolls, list):
        return clean_rolls

    for roll in submitted_rolls[:MAX_ROLLS_PER_POST]:
        if not isinstance(roll, dict):
            continue
        results = roll.get('results')
        label = roll.get('label')
        if not isinstance(results, dict) or not isinstance(label, str):
            continue

        total = 0
        description_parts = []
        valid = True
        for die, values in results.items():
            if die not in DICE_TYPES or not isinstance(values, list):
                valid = False
                break
            sides = DICE_TYPES[die]
            cleaned_values = []
            for v in values:
                if not isinstance(v, int) or not (1 <= v <= sides):
                    valid = False
                    break
                cleaned_values.append(v)
            if not valid:
                break
            total += sum(cleaned_values)
            description_parts.append(f'{len(cleaned_values)}{die} {cleaned_values}')

        if valid and description_parts:
            clean_label = clean_text(label, MAX_ROLL_LABEL_LENGTH) or 'Roll'
            description = ' + '.join(description_parts)
            ability = roll.get('ability')
            if character and ability in ABILITY_KEYS:
                modifier = effective_ability(character, ability)
                total += modifier
                description += f' + {ABILITIES[ABILITY_KEYS.index(ability)]} ({signed(modifier)})'
            manual = roll.get('modifier', 0)
            if (allow_modifier and isinstance(manual, int) and not isinstance(manual, bool)
                    and manual != 0 and abs(manual) <= MAX_ROLL_MODIFIER):
                total += manual
                description += f' + {manual}' if manual > 0 else f' - {-manual}'
            clean_rolls.append({
                'label': clean_label,
                'description': description,
                'total': total
            })

    return clean_rolls


# ---------------------------------------------------------------------------
# Shared page chrome
# ---------------------------------------------------------------------------
# Pop-outs open as real browser windows rather than modals so the DM can drag
# the rules onto a second monitor and leave them there. `window.open` returns
# null when a popup blocker eats it, in which case we fall back to the link's
# normal target=_blank behaviour instead of silently doing nothing.
POPOUT_SCRIPT = """
<script>
    function popout(url, name, width, height) {
        const w = Math.min(width, screen.availWidth);
        const h = Math.min(height, screen.availHeight);
        const win = window.open(
            url, name,
            'width=' + w + ',height=' + h + ',scrollbars=yes,resizable=yes,menubar=no,toolbar=no'
        );
        if (win) { win.focus(); return false; }
        return true;  // blocked — let the browser follow the href instead
    }
</script>
"""

TOP_BAR = """
<div class="topbar">
    <a class="topbar-btn" href="{{ url_for('dm_home') }}">&#9760; DM</a>
    <h1>{{ scene_name }}</h1>
    <div class="topbar-right">
        {% if notes_for == 'dm' %}
            <a class="topbar-btn" href="{{ url_for('dm_players') }}" target="_blank" rel="noopener noreferrer"
               onclick="return popout(this.href, 'morkborg_players', 860, 1000);">&#9760; Players</a>
        {% endif %}
        {% if notes_for %}
            <a class="topbar-btn" href="{{ url_for('notes', who=notes_for) }}" target="_blank" rel="noopener noreferrer"
               onclick="return popout(this.href, 'morkborg_notes_{{ notes_for }}', 520, 640);">&#9998; Notes</a>
        {% endif %}
        <a class="topbar-btn acid" href="{{ url_for('rules') }}" target="_blank" rel="noopener noreferrer"
           onclick="return popout(this.href, 'morkborg_rules', 980, 1000);">&#9670; Rules</a>
    </div>
</div>
"""

SHARED_CSS = """
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=UnifrakturCook:wght@700&family=Barlow+Condensed:ital,wght@0,400;0,600;0,900;1,400;1,900&display=swap" rel="stylesheet">
<style>
    /* Palette and type lifted from the Two Guillians print layout so the
       board and the adventure handouts read as the same object. */
    :root {
        --ink:#08070a;
        --bone:#ded7c4;
        --acid:#f2e50b;
        --rot:#ff2d6f;
        --blood:#8f1109;
        --ash:#6b665e;
        --panel:#100f13;
        --edge:#2a2730;
        --display:"UnifrakturCook","Cloister Black",Impact,serif;
        --body:"Barlow Condensed","Arial Narrow",Haettenschweiler,sans-serif;
    }
    * { box-sizing: border-box; }
    html { background:#17161a; }
    body {
        font-family: var(--body);
        font-size: 17px;
        line-height: 1.3;
        max-width: 1300px;
        margin: 0 auto 40px auto;
        padding: 0 20px;
        background: #17161a;
        color: var(--bone);
        position: relative;
    }
    /* Faint film-grain over the whole page. pointer-events:none keeps it from
       swallowing clicks; fixed so it doesn't scroll and tile-shift. */
    body::before {
        content:""; position: fixed; inset: 0; pointer-events: none; z-index: 0;
        opacity: .09; mix-blend-mode: overlay;
        background-image: url("data:image/svg+xml;utf8,<svg xmlns='http://www.w3.org/2000/svg' width='200' height='200'><filter id='n'><feTurbulence type='fractalNoise' baseFrequency='.85' numOctaves='3'/></filter><rect width='200' height='200' filter='url(%23n)'/></svg>");
    }
    body > * { position: relative; z-index: 1; }

    a { color: var(--acid); }
    a:hover { color: var(--rot); }

    /* --- top bar --- */
    .topbar {
        display: flex;
        align-items: center;
        justify-content: space-between;
        gap: 14px;
        padding: 18px 0 10px;
        border-bottom: 6px solid var(--acid);
        margin-bottom: 22px;
        transform: skewY(-.35deg);
    }
    .topbar > * { transform: skewY(.35deg); }
    .topbar h1 {
        margin: 0;
        font-family: var(--display);
        font-weight: 700;
        font-size: 2.3em;
        line-height: .9;
        color: var(--bone);
        text-align: center;
        flex: 1 1 auto;
        text-shadow: 3px 3px 0 var(--blood);
        word-break: break-word;
    }
    .topbar-btn {
        display: inline-block;
        padding: 9px 15px;
        background: var(--bone);
        color: var(--ink);
        text-decoration: none;
        font-weight: 900;
        font-size: .9em;
        letter-spacing: .14em;
        text-transform: uppercase;
        white-space: nowrap;
        border: 2px solid var(--ink);
        box-shadow: 4px 4px 0 var(--blood);
        flex: 0 0 auto;
    }
    .topbar-right { display: flex; gap: 10px; flex: 0 0 auto; }
    @media (max-width: 600px) {
        /* Title on its own line, buttons share the row below. */
        .topbar { flex-wrap: wrap; }
        .topbar h1 { order: -1; flex: 1 0 100%; text-align: center; }
        .topbar-right { gap: 6px; }
        .topbar-btn { padding-left: 10px; padding-right: 10px; }
    }
    .topbar-btn.acid { background: var(--acid); box-shadow: 4px 4px 0 var(--rot); }
    .topbar-btn:hover { background: var(--rot); color: var(--ink); box-shadow: 4px 4px 0 var(--acid); }

    /* --- forms + cards --- */
    form {
        background: var(--panel);
        padding: 18px;
        border: 3px solid var(--edge);
        margin-bottom: 20px;
    }
    input[type=text], input[type=password], input[type=number], select, textarea {
        width: 100%;
        padding: 8px 10px;
        margin-bottom: 10px;
        box-sizing: border-box;
        border: 2px solid var(--edge);
        border-radius: 0;
        background: #0b0a0d;
        color: var(--bone);
        font-family: var(--body);
        font-size: 1em;
    }
    input:focus, select:focus, textarea:focus {
        outline: none;
        border-color: var(--acid);
        box-shadow: 0 0 0 1px var(--acid);
    }
    textarea { resize: vertical; min-height: 84px; }
    select option { background: #0b0a0d; color: var(--bone); }

    button {
        margin-top: 10px;
        padding: 9px 18px;
        border: 2px solid var(--ink);
        background: var(--acid);
        color: var(--ink);
        cursor: pointer;
        font-family: var(--body);
        font-weight: 900;
        font-size: 1em;
        letter-spacing: .12em;
        text-transform: uppercase;
        box-shadow: 4px 4px 0 var(--blood);
    }
    button:hover { background: var(--rot); box-shadow: 4px 4px 0 var(--acid); }
    button:active { transform: translate(2px, 2px); box-shadow: 2px 2px 0 var(--blood); }
    button.secondary { background: var(--bone); box-shadow: 4px 4px 0 var(--ash); }
    button.secondary:hover { background: var(--acid); }
    button:disabled, button:disabled:hover {
        background: #3a3740; color: #7d7889; box-shadow: none; cursor: not-allowed;
    }

    .char-count { font-size: .85em; color: var(--ash); }
    .hint { color: var(--ash); font-size: .88em; }
    .flash {
        background: var(--blood);
        color: var(--bone);
        border: 2px solid var(--rot);
        padding: 10px 14px;
        margin-bottom: 15px;
        font-weight: 600;
    }
    .card {
        background: var(--panel);
        padding: 15px 18px;
        border: 3px solid var(--edge);
        margin-bottom: 15px;
    }
    h2 {
        font-family: var(--display);
        font-weight: 700;
        font-size: 2em;
        line-height: .95;
        margin: 0 0 4px;
        color: var(--acid);
    }
    h3 {
        margin: 0 0 6px;
        font-weight: 900;
        letter-spacing: .06em;
        text-transform: uppercase;
        font-size: 1.05em;
        color: var(--bone);
    }
    .h-under { height: 4px; background: var(--rot); margin: 0 0 14px; }
    .empty { text-align: center; color: var(--ash); margin-top: 40px; letter-spacing: .16em; text-transform: uppercase; }

    /* --- character sheet --- */
    .sheet-grid {
        display: grid;
        grid-template-columns: repeat(auto-fit, minmax(104px, 1fr));
        gap: 9px;
        margin-bottom: 12px;
    }
    .stat-box {
        text-align: center;
        background: #0b0a0d;
        border: 2px solid var(--edge);
        padding: 8px 6px;
    }
    .stat-box .stat-label {
        font-size: .72em; color: var(--ash); text-transform: uppercase; letter-spacing: .14em;
    }
    .stat-box .stat-value {
        font-size: 1.7em; font-weight: 900; color: var(--acid); line-height: 1.1;
    }
    .stat-box input[type=number] {
        width: 100%;
        border: 2px solid var(--edge);
        text-align: center;
        font-size: 1.3em;
        font-weight: 900;
        color: var(--acid);
        padding: 3px 2px;
        margin-bottom: 0;
    }
    .stat-box.wide { grid-column: span 2; }
    .stat-sub { font-size: .72em; color: var(--ash); }

    .trait-list { display: flex; flex-wrap: wrap; gap: 6px; margin: 10px 0; }
    .trait-pill {
        background: #0b0a0d;
        border: 1px solid var(--edge);
        border-left: 3px solid var(--acid);
        padding: 3px 10px;
        font-size: .88em;
    }
    .trait-pill .trait-key {
        color: var(--ash); margin-right: 6px; text-transform: uppercase;
        font-size: .82em; letter-spacing: .1em;
    }
    .kit-line { margin: 4px 0; font-size: .95em; }
    .kit-line .kit-key {
        color: var(--ash); text-transform: uppercase; letter-spacing: .1em;
        font-size: .8em; margin-right: 6px;
    }
    .kit-line b { color: var(--acid); }
    .class-line {
        color: var(--rot); font-weight: 900; letter-spacing: .14em;
        text-transform: uppercase; font-size: .85em; margin: -2px 0 4px;
    }
    .feature-list { margin: 6px 0 0; padding-left: 18px; font-size: .92em; }
    .feature-list li { margin-bottom: 5px; }
    .feature-list li::marker { color: var(--acid); }
    /* Class rules (always-on) read differently from the one-off kit an
       entry hands you, so they get their own marker colour. */
    .feature-list li.rule { color: #bdb6a6; font-style: italic; }
    .feature-list li.rule::marker { color: var(--rot); }
    .feature-list b { color: var(--acid); }

    .inventory-grid {
        display: grid;
        grid-template-columns: repeat(auto-fit, minmax(150px, 1fr));
        gap: 7px;
        margin-top: 10px;
    }
    .inv-slot label { display: block; font-size: .7em; color: var(--ash); margin-bottom: 2px; letter-spacing: .1em; }
    .inv-slot input { margin-bottom: 0; }
    .inv-status { font-size: .85em; color: var(--acid); margin-top: 8px; min-height: 1.2em; letter-spacing: .08em; }
    .inv-section-head {
        display: flex; justify-content: space-between; align-items: baseline; gap: 10px;
        margin: 16px 0 6px; font-size: .8em; letter-spacing: .12em; text-transform: uppercase; color: var(--ash);
    }
    .inv-section-head b { color: var(--bone); font-size: 1.15em; }
    .inv-section-head .inv-count.full { color: var(--acid); }
    .free-slot { display: flex; align-items: center; gap: 8px; margin: 0 0 8px; }
    .free-slot label {
        flex: 0 0 auto; font-size: .72em; font-weight: 900; letter-spacing: .12em;
        text-transform: uppercase; color: var(--acid);
    }
    .free-slot input { flex: 1 1 auto; margin: 0; }
    .conditions-box { display: flex; flex-wrap: wrap; align-items: center; gap: 6px; margin: 0 0 10px; }
    .conditions-box[hidden] { display: none; }
    .conditions-key { font-size: .72em; font-weight: 900; letter-spacing: .12em; text-transform: uppercase; color: var(--ash); }
    .condition-pill { display: inline-block; padding: 2px 8px; font-size: .85em; border: 2px solid var(--rot); color: var(--bone); }
    .condition-pill b { color: var(--rot); text-transform: uppercase; letter-spacing: .05em; }
    .stat-box.conditioned { outline: 2px dashed var(--rot); outline-offset: -2px; }
    .stat-box.conditioned .stat-value { color: var(--rot); }
    .condition-admin { display: flex; flex-wrap: wrap; align-items: center; gap: 6px; margin: 4px 0; }
    .condition-admin input { margin: 0; width: auto; padding: 5px 6px; font-size: .9em; }
    .condition-admin input[name=name] { flex: 1 1 140px; }
    .condition-admin input[type=number] { width: 58px; }
    .condition-admin label { font-size: .72em; color: var(--ash); text-transform: uppercase; letter-spacing: .08em; }
    .condition-admin button { margin: 0; padding: 5px 10px; font-size: .85em; }
    .stale-notice { display: flex; align-items: center; justify-content: space-between; gap: 10px; }
    .stale-notice[hidden] { display: none; }
    .stale-notice button { margin: 0; }
    .container-box { border-left: 3px solid var(--edge); padding-left: 10px; margin-top: 4px; }
    .container-admin { display: flex; gap: 6px; flex-wrap: wrap; align-items: center; margin: 4px 0; }
    .container-admin input, .container-admin select { margin: 0; width: auto; padding: 5px 6px; font-size: .9em; }
    .container-admin input[name=name] { flex: 1 1 120px; }
    .container-admin input[name=capacity] { width: 64px; }
    .container-admin button { margin: 0; padding: 5px 10px; font-size: .85em; }
    .encumbrance { font-size: .85em; color: var(--ash); margin-top: 8px; letter-spacing: .06em; }
    .encumbrance.over { color: var(--rot); font-weight: 900; }
    .encumbrance.impossible { color: var(--bone); background: var(--blood); padding: 3px 8px; font-weight: 900; }

    .broken-banner {
        background: var(--blood); color: var(--bone); border: 2px solid var(--rot);
        padding: 8px 12px; margin-bottom: 12px; font-weight: 900;
        letter-spacing: .1em; text-transform: uppercase;
    }

    /* --- posts --- */
    .post-header {
        display: flex;
        justify-content: space-between;
        align-items: center;
        gap: 10px;
        font-size: .9em;
        color: var(--ash);
        margin-bottom: 8px;
        border-bottom: 1px solid var(--edge);
        padding-bottom: 6px;
    }
    .post-header-left { display: flex; align-items: center; gap: 8px; }
    .username { font-weight: 900; letter-spacing: .06em; text-transform: uppercase; }
    .char-class { color: var(--ash); font-weight: 400; font-size: .9em; }
    .timestamp { white-space: nowrap; font-size: .85em; }
    .dm-username {
        font-weight: 900; color: var(--ink); background: var(--acid);
        padding: 2px 9px; letter-spacing: .1em; text-transform: uppercase;
    }
    .whisper-badge {
        font-weight: 900; color: var(--ink); background: var(--rot);
        padding: 3px 10px; font-size: .85em; letter-spacing: .08em; text-transform: uppercase;
    }
    .card.whisper-card { border: 3px dashed var(--rot); }
    .whisper-toggle {
        display: inline-flex; align-items: center; gap: 7px; margin: 10px 14px 0 0; cursor: pointer;
        font-weight: 900; font-size: .85em; letter-spacing: .08em; text-transform: uppercase; color: var(--ash);
    }
    .whisper-toggle input { width: auto; margin: 0; }
    .whisper-toggle.on { color: var(--rot); }
    #postForm.whispering { border: 3px dashed var(--rot); }
    .post-target { display: flex; align-items: center; gap: 10px; margin-bottom: 10px; }
    .post-target span { flex: 0 0 auto; font-weight: 900; font-size: .8em; letter-spacing: .12em;
                        text-transform: uppercase; color: var(--ash); }
    .post-target select { flex: 1 1 auto; margin: 0; }
    #dmPostCard.whispering { border: 3px dashed var(--rot); }
    #dmPostCard.whispering .post-target span { color: var(--rot); }
    .whisper-btn { background: var(--rot); box-shadow: 4px 4px 0 var(--acid); }
    .whisper-btn:hover { background: var(--acid); box-shadow: 4px 4px 0 var(--rot); }
    .message { white-space: pre-wrap; word-wrap: break-word; }
    .message strong { color: var(--acid); font-weight: 900; }
    .message em { color: #efe9d8; }
    .message .mention { padding: 0 4px; font-weight: 900; }
    .edited-mark { margin-left: 6px; font-size: .75em; color: var(--ash); font-style: italic; }
    .own-actions { display: inline-flex; gap: 6px; margin-left: 8px; }
    .own-actions button { margin: 0; padding: 1px 8px; font-size: .72em; box-shadow: none; }
    .post-edit textarea { margin-bottom: 6px; min-height: 70px; }
    .post-edit .post-edit-bar { display: flex; gap: 8px; align-items: center; flex-wrap: wrap; }
    .post-edit button { margin: 0; padding: 4px 12px; font-size: .85em; }
    .post-edit .post-edit-error { color: var(--rot); font-size: .85em; }
    .mention-wrap { position: relative; }
    .mention-menu {
        position: absolute; left: 0; right: 0; z-index: 50; margin-top: -6px;
        max-height: 220px; overflow-y: auto; background: var(--ink);
        border: 2px solid var(--acid); box-shadow: 4px 4px 0 var(--blood);
    }
    .mention-menu[hidden] { display: none; }
    .mention-option {
        display: block; width: 100%; margin: 0; padding: 7px 10px; text-align: left;
        background: transparent; border: none; box-shadow: none; font-weight: 900;
        font-size: 1em; letter-spacing: .03em; text-transform: none; cursor: pointer;
    }
    .mention-option.active, .mention-option:hover { background: var(--edge); }
    .delete-post-form { display: inline; margin: 0; padding: 0; background: none; border: none; }
    .plain-form { margin: 0; padding: 0; background: none; border: none; }
    .delete-post-btn {
        margin: 0; padding: 2px 9px; background: var(--blood); color: var(--bone);
        font-size: .72em; box-shadow: 2px 2px 0 var(--ink);
    }
    .delete-post-btn:hover { background: var(--rot); color: var(--ink); box-shadow: 2px 2px 0 var(--ink); }

    /* --- dice roller --- */
    .dice-roller { border: 2px solid var(--edge); padding: 14px; margin-bottom: 15px; background: #0b0a0d; }
    .dice-roller h3 { margin: 0 0 10px 0; font-size: .95em; color: var(--acid); }
    .dice-grid { display: grid; grid-template-columns: repeat(auto-fit, minmax(64px, 1fr)); gap: 8px; margin-bottom: 10px; }
    .dice-cell { text-align: center; }
    .dice-cell label { display: block; font-size: .85em; font-weight: 900; margin-bottom: 4px; color: var(--acid); letter-spacing: .08em; }
    .dice-cell input[type=number] { text-align: center; margin-bottom: 0; padding: 6px 2px; }
    .pending-rolls { margin-top: 10px; }
    .roll-item {
        display: flex; justify-content: space-between; align-items: center;
        background: var(--panel); border: 2px solid var(--edge);
        padding: 7px 9px; margin-bottom: 6px; font-size: .9em; gap: 8px;
    }
    .roll-item .roll-label-input { width: 130px; flex: 0 0 auto; margin-bottom: 0; padding: 5px 6px; font-size: .9em; }
    .roll-item .roll-desc { flex: 1 1 auto; }
    .roll-item .remove-btn { margin: 0; padding: 2px 8px; background: var(--blood); color: var(--bone); flex: 0 0 auto; box-shadow: 2px 2px 0 var(--ink); }
    .roll-item .remove-btn:hover { background: var(--rot); color: var(--ink); }
    .post-rolls { margin-top: 10px; }
    .roll-badge {
        display: block; background: #0b0a0d; border-left: 4px solid var(--acid);
        padding: 6px 10px; margin-top: 6px; font-size: .88em; font-family: ui-monospace, monospace;
        color: #bdb6a6;
    }
    .roll-badge .roll-total { font-weight: 900; color: var(--acid); font-size: 1.15em; }

    /* --- creation wizard --- */
    .wizard-step { border-left: 4px solid var(--edge); padding-left: 15px; margin-bottom: 22px; }
    .wizard-step.done { border-left-color: var(--acid); }
    .wizard-step h3 { font-size: 1em; margin-bottom: 8px; }
    .wizard-step h3 .step-num { color: var(--rot); margin-right: 6px; }
    .roll-result { background: #0b0a0d; border: 2px solid var(--edge); padding: 12px; margin-top: 10px; }
    .roll-result ul { margin: 6px 0 0; padding-left: 18px; }
    .roll-result li { margin-bottom: 3px; }
    .roll-result li::marker { color: var(--acid); }
    .name-row { display: flex; gap: 8px; align-items: flex-start; }
    .name-row input { flex: 1 1 auto; }
    .name-row button { margin-top: 0; flex: 0 0 auto; }
    .ability-picker { display: flex; flex-wrap: wrap; gap: 8px; margin: 10px 0; }
    .ability-check {
        display: flex; align-items: center; gap: 6px; padding: 6px 11px;
        border: 2px solid var(--edge); background: #0b0a0d; cursor: pointer;
        text-transform: uppercase; letter-spacing: .08em; font-size: .85em; font-weight: 900;
    }
    .ability-check.on { border-color: var(--acid); color: var(--acid); }
    .ability-check input { width: auto; margin: 0; }

    /* --- DM view --- */
    .dm-char-card { border-left: 6px solid var(--acid); }
    .dm-char-card.dead-card { border-left-color: var(--ash); opacity: .7; }
    .dead-badge { color: var(--rot); font-weight: 900; letter-spacing: .08em; }
    .stats-edit-form { background: transparent; padding: 0; border: none; margin-bottom: 10px; }
    .dm-actions { display: flex; gap: 8px; margin-top: 8px; flex-wrap: wrap; }
    .revive-btn { background: var(--bone); }
    .dm-inv-form { background: transparent; padding: 0; border: none; margin: 6px 0 0 0; }
    .dm-inv-grid { display: grid; grid-template-columns: repeat(auto-fit, minmax(140px, 1fr)); gap: 7px; margin-bottom: 8px; }
    .dm-inv-grid label { display: block; font-size: .7em; color: var(--ash); margin-bottom: 2px; }
    .dm-inv-grid input { margin-bottom: 0; }
    .dm-attach { margin-top: 12px; padding-top: 10px; border-top: 1px solid var(--edge); }
    .attach-badge {
        display: inline-block; padding: 3px 10px; font-size: .78em; font-weight: 900;
        background: var(--edge); color: var(--ash); margin-right: 8px;
        letter-spacing: .08em; text-transform: uppercase;
    }
    .attach-badge.attached { background: var(--acid); color: var(--ink); }
    .login-row { display: flex; gap: 6px; margin-top: 8px; align-items: center; flex-wrap: wrap; }
    .login-field { flex: 1 1 140px; font-family: ui-monospace, monospace; font-size: .85em; margin-bottom: 0; }
    .login-row .login-key { flex: 0 0 auto; font-size: .72em; color: var(--ash); text-transform: uppercase; letter-spacing: .1em; }
    .login-row button { margin: 0; }
    .sheet-login { margin-top: 14px; padding-top: 10px; border-top: 1px solid var(--edge); font-size: .85em; color: var(--ash); }
    .sheet-login code { color: var(--bone); font-family: ui-monospace, monospace; }
    .sheet-login details summary { cursor: pointer; text-transform: uppercase; letter-spacing: .1em; font-size: .85em; }
    .sheet-login form { display: inline; }
    .sheet-login button { margin: 8px 0 0; padding: 4px 12px; font-size: .85em; }
    .roll-item .roll-stat-select { width: auto; flex: 0 0 auto; margin-bottom: 0; padding: 5px 6px; font-size: .9em; }
    .login-card form { display: flex; gap: 8px; flex-wrap: wrap; align-items: flex-start; }
    .login-card input { flex: 1 1 160px; }
    .login-card button { margin-top: 0; }

    /* --- pop-out button shelf (DM tools) --- */
    .shelf { display: flex; flex-wrap: wrap; gap: 9px; margin-top: 6px; }
    .docs-card { padding-top: 12px; padding-bottom: 12px; }
    .docs-card h3 { margin: 0 0 6px; }
    .docs-card .shelf { gap: 6px; margin-top: 0; }
    .docs-card .shelf-btn { padding: 4px 10px; font-size: .78em; box-shadow: none; }
    .shelf-btn {
        display: inline-block; padding: 9px 14px; background: var(--bone); color: var(--ink);
        text-decoration: none; font-weight: 900; font-size: .85em; letter-spacing: .1em;
        text-transform: uppercase; border: 2px solid var(--ink); box-shadow: 4px 4px 0 var(--blood);
    }
    .shelf-btn:hover { background: var(--acid); color: var(--ink); box-shadow: 4px 4px 0 var(--rot); }
    .shelf-btn.pending {
        background: transparent; color: var(--ash); border: 2px dashed var(--ash);
        box-shadow: none; cursor: not-allowed;
    }
    .shelf-btn.pending:hover { background: transparent; color: var(--ash); box-shadow: none; }

    /* --- death screen --- */
    .death-card { text-align: center; padding: 44px 20px; border-color: var(--blood); }
    .death-card h2 { font-size: 3.2em; color: var(--rot); }
    .death-card .skull { font-size: 3.4em; margin-bottom: 6px; }

    /* --- two-column layout: sheet/posting left, scrollable feed right --- */
    .layout { display: flex; gap: 24px; align-items: flex-start; }
    .layout-left { flex: 1 1 420px; min-width: 320px; max-width: 480px; }
    .layout-right { flex: 2 1 500px; min-width: 0; position: sticky; top: 20px; }
    .layout-right h2 { margin-top: 0; }
    .feed-scroll { max-height: calc(100vh - 60px); overflow-y: auto; padding-right: 6px; }
    .feed-scroll::-webkit-scrollbar { width: 10px; }
    .feed-scroll::-webkit-scrollbar-track { background: #0b0a0d; }
    .feed-scroll::-webkit-scrollbar-thumb { background: var(--edge); }
    .feed-scroll::-webkit-scrollbar-thumb:hover { background: var(--acid); }

    /* Phone layout: Feed / Sheet tabs. Hidden on desktop, where both show. */
    .mobile-tabs { display: none; }
    @media (max-width: 850px) {
        .mobile-tabs {
            display: flex; position: sticky; top: 0; z-index: 40; gap: 0; margin: 0 0 12px;
            background: var(--ink); border-bottom: 3px solid var(--edge);
            padding-top: env(safe-area-inset-top, 0px);
        }
        .mobile-tabs button {
            flex: 1 1 0; margin: 0; padding: 12px 0; box-shadow: none; border: none;
            background: transparent; color: var(--ash); font-size: 1em; letter-spacing: .15em;
        }
        .mobile-tabs button.active { color: var(--ink); background: var(--acid); }
        .tab-dot { display: inline-block; width: 8px; height: 8px; margin-left: 6px; vertical-align: middle;
                   border-radius: 50%; background: var(--rot); }
        .tab-dot[hidden] { display: none; }
        body.tab-feed #sheetCard { display: none; }
        body.tab-sheet #postForm, body.tab-sheet .layout-right { display: none; }
        body.tab-feed .dm-table-card { display: none; }
        body.tab-table #dmPostCard, body.tab-table .layout-right { display: none; }
    }
    @media (max-width: 850px) {
        .layout { flex-direction: column; }
        .layout-left { max-width: none; width: 100%; }
        .layout-right { position: static; width: 100%; }
        .feed-scroll { max-height: 70vh; }
        .topbar h1 { font-size: 1.5em; }
    }
</style>
"""


FAVICON = ('<link rel="icon" href="data:image/svg+xml,'
           '<svg xmlns=%22http://www.w3.org/2000/svg%22 viewBox=%220 0 100 100%22>'
           '<text y=%22.9em%22 font-size=%2290%22>&#128128;</text></svg>">')

# ---------------------------------------------------------------------------
# TEMPLATE: character creation wizard
# ---------------------------------------------------------------------------
CREATE_TEMPLATE = """
<!doctype html>
<html lang="en">
<head>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <title>Create a Scvm</title>
""" + FAVICON + SHARED_CSS + POPOUT_SCRIPT + """
</head>
<body>
""" + TOP_BAR + """
    {% with messages = get_flashed_messages() %}
        {% if messages %}
            {% for m in messages %}<div class="flash">{{ m }}</div>{% endfor %}
        {% endif %}
    {% endwith %}

    <div class="card login-card">
        <h2>Log In</h2>
        <div class="h-under"></div>
        <p class="hint">Already have a character? Use the username and password you were given
           when it was created. The DM can look them up if you've lost them.</p>
        <form method="POST" action="{{ url_for('player_login') }}">
            <input type="text" name="username" placeholder="Username" autocomplete="username"
                   autocapitalize="none" spellcheck="false" maxlength="64" required>
            <input type="password" name="password" placeholder="Password" autocomplete="current-password"
                   maxlength="64" required>
            <button type="submit">Log In</button>
        </form>
    </div>

    <div class="card">
        <h2>Create a Scvm</h2>
        <div class="h-under"></div>
        <p class="hint">Character creation from the MÖRK BORG Bare Bones Edition, with or without a class.
           You need a character before you can post to the board.
           <a href="{{ url_for('rules') }}" target="_blank" rel="noopener noreferrer"
              onclick="return popout(this.href, 'morkborg_rules', 980, 1000);">Open the rules</a>.</p>

        <form method="POST" action="{{ url_for('finish_character') }}" id="createForm">

            <div class="wizard-step" id="stepClass">
                <h3><span class="step-num">I</span> Class</h3>
                <p class="hint">Classes are optional. Each one fixes your HP, silver and Omen dice,
                   adjusts your ability rolls and brings its own gear.</p>
                <div class="name-row">
                    <select id="classSelect" onchange="showClass()">
                        <option value="">No class &mdash; classless</option>
                        {% for name in class_names %}
                            <option value="{{ name }}">{{ name }}</option>
                        {% endfor %}
                    </select>
                    <button type="button" class="secondary" onclick="rollClass()">&#9860; Roll</button>
                </div>
                <div class="roll-result" id="classResult"></div>
            </div>

            <div class="wizard-step" id="stepName">
                <h3><span class="step-num">II</span> Name</h3>
                <p class="hint">Name your character if you wish. It will not save you.</p>
                <div class="name-row">
                    <input type="text" name="name" id="nameInput" placeholder="Name your character"
                           maxlength="__MAX_USERNAME_LENGTH__" required>
                    <button type="button" class="secondary" onclick="rollName()">&#9860; Roll</button>
                </div>
            </div>

            <div class="wizard-step" id="stepAbilities">
                <h3><span class="step-num">III</span> Abilities</h3>
                <p class="hint">Each ability is 3d6 read off the score table, giving a modifier from &minus;3 to +3.</p>
                <div id="pickerWrap">
                <p class="hint">Playing without a class, two abilities may be rolled 4d6 and drop the
                   lowest die &mdash; choose those two:</p>
                <div class="ability-picker" id="abilityPicker">
                    {% for key, label in ability_choices %}
                        <label class="ability-check" data-key="{{ key }}">
                            <input type="checkbox" value="{{ key }}" onchange="syncPicker()"> {{ label }}
                        </label>
                    {% endfor %}
                </div>
                </div>
                <p class="hint" id="classAbilityNote" style="display:none;"></p>
                <button type="button" id="rollAbilitiesBtn" onclick="rollAbilities()" disabled>&#9860; Roll Abilities, HP &amp; Silver</button>
                <div class="roll-result" id="abilitiesResult" style="display:none;"></div>
            </div>

            <div class="wizard-step" id="stepGear">
                <h3><span class="step-num">IV</span> Kit, Weapon &amp; Armor</h3>
                <p class="hint">Some starting gear scales with Presence, so roll your abilities first.</p>
                <button type="button" id="rollGearBtn" onclick="rollGear()" disabled>&#9860; Roll Equipment</button>
                <div class="roll-result" id="gearResult" style="display:none;"></div>
            </div>

            <div class="wizard-step" id="stepFlavour">
                <h3><span class="step-num">V</span> Wretched Details <span class="hint">(optional)</span></h3>
                <p class="hint">A terrible trait, a broken body and a bad habit. Skip it if you'd rather invent your own.</p>
                <button type="button" class="secondary" onclick="rollFlavour()">&#9860; Roll the Optional Tables</button>
                <div class="roll-result" id="flavourResult" style="display:none;"></div>
            </div>

            <button type="submit" id="finishBtn" disabled>Loose it upon the world</button>
        </form>
    </div>

    <script>
        const MAX_BOOSTED = 2;
        const CLASS_INFO = {{ class_info | tojson }};

        function currentClass() {
            return document.getElementById('classSelect').value;
        }

        function showClass() {
            const name = currentClass();
            const info = CLASS_INFO[name];
            const box = document.getElementById('classResult');
            let html = '';
            if (info.blurb) {
                html += '<p style="margin-bottom:8px;"><em>' + info.blurb + '</em></p>';
            }
            html += '<ul>' + info.bullets.map(b => '<li>' + b + '</li>').join('') + '</ul>';
            box.innerHTML = html;
            box.style.display = 'block';

            // The 4d6-drop-lowest pick is a classless-only option; a class
            // brings its own fixed ability modifiers instead.
            const classed = name !== '';
            document.getElementById('pickerWrap').style.display = classed ? 'none' : 'block';
            const note = document.getElementById('classAbilityNote');
            if (classed && info.ability_note) {
                note.textContent = info.ability_note;
                note.style.display = 'block';
            } else {
                note.style.display = 'none';
            }

            // Changing class invalidates anything already rolled off it.
            resetFrom('abilities');
            syncPicker();
        }

        function rollClass() {
            const select = document.getElementById('classSelect');
            const names = Object.keys(CLASS_INFO).filter(n => n !== '');
            select.value = names[Math.floor(Math.random() * names.length)];
            showClass();
        }

        function resetFrom(step) {
            const boxes = step === 'abilities'
                ? ['abilitiesResult', 'gearResult']
                : ['gearResult'];
            boxes.forEach(id => {
                const el = document.getElementById(id);
                el.dataset.done = '';
                el.style.display = 'none';
            });
            document.getElementById('stepAbilities').classList.remove('done');
            document.getElementById('stepGear').classList.remove('done');
            document.getElementById('rollGearBtn').disabled = true;
            checkReady();
        }

        function syncPicker() {
            if (currentClass() !== '') {
                // A class rolls straight away — nothing to choose.
                document.getElementById('rollAbilitiesBtn').disabled = false;
                return;
            }
            const boxes = Array.from(document.querySelectorAll('#abilityPicker input'));
            const chosen = boxes.filter(b => b.checked);
            // Only ever two abilities get the 4d6 treatment, so once two are
            // ticked the rest are locked rather than silently ignored.
            boxes.forEach(b => { b.disabled = !b.checked && chosen.length >= MAX_BOOSTED; });
            boxes.forEach(b => b.closest('.ability-check').classList.toggle('on', b.checked));
            document.getElementById('rollAbilitiesBtn').disabled = chosen.length !== MAX_BOOSTED;
        }

        function checkReady() {
            const abilities = document.getElementById('abilitiesResult').dataset.done === '1';
            const gear = document.getElementById('gearResult').dataset.done === '1';
            document.getElementById('finishBtn').disabled = !(abilities && gear);
        }

        async function postJson(url, payload) {
            const resp = await fetch(url, {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify(payload || {})
            });
            if (!resp.ok) {
                const err = await resp.json().catch(() => ({}));
                throw new Error(err.error || 'That roll failed. Try again.');
            }
            return resp.json();
        }

        async function rollName() {
            try {
                const data = await postJson('{{ url_for("roll_name") }}');
                document.getElementById('nameInput').value = data.name;
            } catch (e) { alert(e.message); }
        }

        async function rollAbilities() {
            const boosted = Array.from(document.querySelectorAll('#abilityPicker input:checked')).map(b => b.value);
            try {
                const data = await postJson('{{ url_for("roll_abilities") }}',
                                            { boosted: boosted, class_name: currentClass() });
                const box = document.getElementById('abilitiesResult');
                let html = '<div class="sheet-grid">';
                data.abilities.forEach(function (a) {
                    html += '<div class="stat-box"><div class="stat-label">' + a.label + '</div>' +
                            '<div class="stat-value">' + a.display + '</div>' +
                            '<div class="stat-sub">' + a.detail + '</div></div>';
                });
                html += '</div><div class="sheet-grid">' +
                        '<div class="stat-box"><div class="stat-label">HP</div><div class="stat-value">' + data.hp +
                        '</div><div class="stat-sub">Toughness + d' + data.hp_die + '</div></div>' +
                        '<div class="stat-box"><div class="stat-label">Omens</div><div class="stat-value">' + data.omens +
                        '</div><div class="stat-sub">d2</div></div>' +
                        '<div class="stat-box"><div class="stat-label">Silver</div><div class="stat-value">' + data.silver +
                        '</div><div class="stat-sub">s</div></div></div>';
                box.innerHTML = html;
                box.style.display = 'block';
                box.dataset.done = '1';
                document.getElementById('stepAbilities').classList.add('done');
                document.getElementById('rollGearBtn').disabled = false;
                // Presence feeds the gear counts, so a re-roll invalidates any
                // equipment already rolled against the old value.
                const gearBox = document.getElementById('gearResult');
                gearBox.dataset.done = '';
                gearBox.style.display = 'none';
                document.getElementById('stepGear').classList.remove('done');
                checkReady();
            } catch (e) { alert(e.message); }
        }

        async function rollGear() {
            try {
                const data = await postJson('{{ url_for("roll_gear") }}');
                const box = document.getElementById('gearResult');
                let html = '';
                if (data.origin) {
                    html += '<div class="kit-line"><span class="kit-key">' + data.origin_label +
                            '</span>' + data.origin + '</div>';
                }
                html += '<div class="kit-line"><span class="kit-key">Weapon</span><b>' + data.weapon + '</b></div>';
                html += '<div class="kit-line"><span class="kit-key">Armor</span><b>' + data.armor + '</b></div>';
                html += '<div class="kit-line"><span class="kit-key">Carried in</span>' + data.container + '</div>';
                html += '<div class="kit-line"><span class="kit-key">Food</span>' + data.food + ' days, plus a waterskin</div>';
                html += '<ul>';
                data.items.forEach(function (item) { html += '<li>' + item + '</li>'; });
                html += '</ul>';
                if (data.features && data.features.length) {
                    html += '<div class="kit-line" style="margin-top:10px;"><span class="kit-key">' +
                            (data.feature_label || 'Class features') + '</span></div>';
                    html += '<ul>';
                    data.features.forEach(function (f) {
                        html += '<li><b>' + f.name + '</b> &mdash; ' + f.description + '</li>';
                    });
                    html += '</ul>';
                }
                box.innerHTML = html;
                box.style.display = 'block';
                box.dataset.done = '1';
                document.getElementById('stepGear').classList.add('done');
                checkReady();
            } catch (e) { alert(e.message); }
        }

        async function rollFlavour() {
            try {
                const data = await postJson('{{ url_for("roll_flavour") }}');
                const box = document.getElementById('flavourResult');
                let html = '<div class="trait-list">';
                data.traits.forEach(function (t) {
                    html += '<span class="trait-pill"><span class="trait-key">' + t.key + '</span>' + t.value + '</span>';
                });
                html += '</div>';
                box.innerHTML = html;
                box.style.display = 'block';
                box.dataset.done = '1';
                document.getElementById('stepFlavour').classList.add('done');
            } catch (e) { alert(e.message); }
        }

        showClass();
    </script>
</body>
</html>
"""

CREATE_TEMPLATE = CREATE_TEMPLATE.replace('__MAX_USERNAME_LENGTH__', str(MAX_USERNAME_LENGTH))


# ---------------------------------------------------------------------------
# TEMPLATE: main board (character sheet + posting + dice + messages)
# ---------------------------------------------------------------------------
# @mention picker, shared by the board and the DM dashboard. Attaches to
# every message box on the page: typing @ lists living characters, narrowed
# as you type; arrow keys / Enter / Tab / click insert the name, Esc closes.
# Names come from /api/mentions so characters created after the page loaded
# still show up. Rendering of mentions is unchanged (format_message).
MENTION_SCRIPT = """
<script>
// Apply edits and deletions reported by /api/feed to the cards on screen.
// Shared by the board and the DM dashboard (each passes its own builder).
// A card someone is in the middle of editing is left alone.
function applyFeedChanges(data, build) {
    (data.deleted || []).forEach(function (id) {
        const card = document.querySelector('#feedScroll [data-post-id="' + CSS.escape(id) + '"]');
        if (card) card.remove();
    });
    (data.updates || []).forEach(function (post) {
        const card = document.querySelector('#feedScroll [data-post-id="' + CSS.escape(post.id) + '"]');
        if (card && !card.querySelector('.post-edit')) card.replaceWith(build(post));
    });
}
</script>
<script>
(function () {
    const URL = '{{ url_for("api_mentions") }}';
    const SELF = {{ (mention_self or '') | tojson }}.toLowerCase();
    let names = [];
    let fetchedAt = 0;

    async function loadNames(force) {
        if (!force && Date.now() - fetchedAt < 20000) return;
        fetchedAt = Date.now();
        try {
            const resp = await fetch(URL);
            if (resp.ok) names = (await resp.json()).characters || [];
        } catch (e) { /* keep the last list */ }
    }

    // The @query being typed at the caret, or null. The @ must start the
    // text or follow whitespace, and the query can contain spaces (names do)
    // but not line breaks.
    function currentQuery(box) {
        const upto = box.value.slice(0, box.selectionStart);
        const at = upto.lastIndexOf('@');
        if (at < 0 || (at > 0 && !/\\s/.test(upto[at - 1]))) return null;
        const query = upto.slice(at + 1);
        if (query.length > 30 || /\\n/.test(query)) return null;
        return { start: at, query: query };
    }

    function attach(box) {
        const wrap = document.createElement('div');
        wrap.className = 'mention-wrap';
        box.parentNode.insertBefore(wrap, box);
        wrap.appendChild(box);
        const menu = document.createElement('div');
        menu.className = 'mention-menu';
        menu.hidden = true;
        menu.setAttribute('role', 'listbox');
        wrap.appendChild(menu);

        let matches = [];
        let active = 0;
        let at = null;

        function close() { menu.hidden = true; matches = []; at = null; }

        function draw() {
            menu.replaceChildren(...matches.map(function (m, i) {
                const opt = document.createElement('button');
                opt.type = 'button';
                opt.className = 'mention-option' + (i === active ? ' active' : '');
                opt.setAttribute('role', 'option');
                opt.textContent = '@' + m.name;
                if (m.color) opt.style.color = m.color;
                // mousedown, not click, so the textarea keeps focus.
                opt.addEventListener('mousedown', function (e) { e.preventDefault(); choose(i); });
                return opt;
            }));
            menu.hidden = matches.length === 0;
            const current = menu.children[active];
            if (current) current.scrollIntoView({ block: 'nearest' });
        }

        function update() {
            at = currentQuery(box);
            if (!at) { close(); return; }
            const q = at.query.toLowerCase();
            const pool = names.filter(n => n.name.toLowerCase() !== SELF);
            matches = pool.filter(n => n.name.toLowerCase().startsWith(q))
                .concat(pool.filter(n => !n.name.toLowerCase().startsWith(q) && n.name.toLowerCase().includes(q)))
                .slice(0, 8);
            active = 0;
            draw();
        }

        function choose(i) {
            const m = matches[i];
            if (!m || !at) return;
            const before = box.value.slice(0, at.start);
            const after = box.value.slice(box.selectionStart);
            const insert = '@' + m.name + (after.startsWith(' ') ? '' : ' ');
            const next = before + insert + after;
            if (box.maxLength > 0 && next.length > box.maxLength) { close(); return; }
            box.value = next;
            const caret = before.length + insert.length;
            box.setSelectionRange(caret, caret);
            close();
            box.dispatchEvent(new Event('input', { bubbles: true }));  // update counters
            box.focus();
        }

        box.addEventListener('focus', () => loadNames(false));
        box.addEventListener('input', update);
        box.addEventListener('click', update);
        box.addEventListener('blur', close);
        box.addEventListener('keydown', function (e) {
            if (menu.hidden) return;
            if (e.key === 'ArrowDown') { active = (active + 1) % matches.length; draw(); e.preventDefault(); }
            else if (e.key === 'ArrowUp') { active = (active - 1 + matches.length) % matches.length; draw(); e.preventDefault(); }
            else if (e.key === 'Enter' || e.key === 'Tab') { choose(active); e.preventDefault(); }
            else if (e.key === 'Escape') { close(); e.preventDefault(); }
        });
    }

    document.querySelectorAll('textarea[name="message"]').forEach(attach);
    loadNames(true);
})();
</script>
"""

BOARD_TEMPLATE = """
<!doctype html>
<html lang="en">
<head>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <title>{{ scene_name }}</title>
""" + FAVICON + SHARED_CSS + POPOUT_SCRIPT + """
</head>
<body>
""" + TOP_BAR + """
    {% with messages = get_flashed_messages() %}
        {% if messages %}
            {% for m in messages %}<div class="flash">{{ m }}</div>{% endfor %}
        {% endif %}
    {% endwith %}

    <nav class="mobile-tabs" role="tablist" aria-label="Board">
        <button type="button" role="tab" data-tab="feed">Feed<span class="tab-dot" hidden></span></button>
        <button type="button" role="tab" data-tab="sheet">Sheet<span class="tab-dot" hidden></span></button>
    </nav>
    <div class="layout">
    <div class="layout-left">

    <div class="card" id="sheetCard">
        <h2 style="color: {{ character.color }};">{{ character.name }}</h2>
        {% if character.class_name %}
            <div class="class-line">{{ character.class_name }}</div>
        {% endif %}
        <div class="h-under"></div>

        <div class="flash stale-notice" id="sheetNotice" hidden>
            <span id="sheetNoticeText">The DM changed your sheet.</span>
            <button type="button" class="secondary" onclick="window.location.reload();">Reload</button>
        </div>
        <div class="broken-banner" id="brokenBanner" style="display:{{ 'block' if character.hp == 0 else 'none' }};">
            &#9760; Broken &mdash; roll d4 on the Broken table
        </div>

        <div class="conditions-box" id="conditionsBox" {{ 'hidden' if not conditions else '' }}>
            <span class="conditions-key">Conditions</span>
            <span id="conditionsList">
                {% for c in conditions %}
                    <span class="condition-pill"><b>{{ c.name }}</b>{% if c.summary %} {{ c.summary }}{% endif %}</span>
                {% endfor %}
            </span>
        </div>

        <div class="sheet-grid">
            {% for key, label in ability_pairs %}
                <div class="stat-box{{ ' conditioned' if effective[key] != character[key] else '' }}" id="ability-{{ key }}">
                    <div class="stat-label">{{ label }}</div>
                    <div class="stat-value">{{ effective[key] | signed }}</div>
                    <div class="stat-sub">{% if effective[key] != character[key] %}base {{ character[key] | signed }}{% endif %}</div>
                </div>
            {% endfor %}
        </div>

        <div class="sheet-grid">
            <div class="stat-box">
                <div class="stat-label">HP</div>
                <input type="number" id="hpInput" value="{{ character.hp }}" min="__MIN_HP__" max="__MAX_HP__">
                <div class="stat-sub">max {{ character.max_hp }}</div>
            </div>
            <div class="stat-box">
                <div class="stat-label">Omens</div>
                <input type="number" id="omensInput" value="{{ character.omens }}" min="0" max="99">
                <div class="stat-sub">regain d2 on rest</div>
            </div>
            <div class="stat-box">
                <div class="stat-label">Silver</div>
                <input type="number" id="silverInput" value="{{ character.silver }}" min="0" max="__MAX_SILVER__">
                <div class="stat-sub">s</div>
            </div>
        </div>

        <div class="kit-line"><span class="kit-key">Weapon</span><b>{{ character.weapon }}</b></div>
        <div class="kit-line"><span class="kit-key">Armor</span><b>{{ character.armor }}</b></div>

        {% if character.traits %}
            <div class="trait-list">
                {% for key, val in character.traits.items() %}
                    <span class="trait-pill"><span class="trait-key">{{ key }}</span>{{ val }}</span>
                {% endfor %}
            </div>
        {% endif %}

        {% if character.origin %}
            <div class="kit-line"><span class="kit-key">Origin</span>{{ character.origin }}</div>
        {% endif %}

        {% if character.features or character.class_traits %}
            <h3>Class Features</h3>
            <ul class="feature-list">
                {% for t in character.class_traits %}
                    <li class="rule">{{ t }}</li>
                {% endfor %}
                {% for f in character.features %}
                    <li><b>{{ f.name }}</b> &mdash; {{ f.description }}</li>
                {% endfor %}
            </ul>
        {% endif %}

        <h3>Inventory</h3>
        <div class="inv-section-head"><b>On your person</b><span>Strength + 8 = <span id="capacityLabel">{{ capacity }}</span></span></div>
        <div class="free-slot" title="Something nearly weightless — a ring, a letter, a key. Doesn't count toward your capacity.">
            <label for="freeItem">Free</label>
            <input type="text" class="inv-input" id="freeItem" data-section="free"
                   maxlength="{{ max_item_len }}" value="{{ character.free_item }}"
                   placeholder="Something nearly weightless">
        </div>
        <div class="inventory-grid" id="inventoryGrid">
            {% for i in range(slot_count) %}
                <div class="inv-slot">
                    <label>{{ i + 1 }}</label>
                    <input type="text" class="inv-input" data-section="person"
                           maxlength="{{ max_item_len }}" value="{{ character.inventory[i] }}"
                           placeholder="&mdash;">
                </div>
            {% endfor %}
        </div>
        <div class="encumbrance" id="encumbrance"></div>

        {% for c in character.containers %}
            <div class="container-box">
                <div class="inv-section-head">
                    <b>{{ c.name }}</b>
                    <span class="inv-count" data-count-for="{{ c.id }}" data-capacity="{{ c.capacity }}"></span>
                </div>
                <div class="inventory-grid">
                    {% for item in c['items'] %}
                        <div class="inv-slot">
                            <label>{{ loop.index }}</label>
                            <input type="text" class="inv-input" data-section="{{ c.id }}"
                                   maxlength="{{ max_item_len }}" value="{{ item }}" placeholder="&mdash;">
                        </div>
                    {% endfor %}
                </div>
            </div>
        {% endfor %}
        <div class="inv-status" id="invStatus"></div>

        <div class="sheet-login">
            <details>
                <summary>Your login</summary>
                <div>Username <code>{{ character.username }}</code></div>
                <div>Password <code>{{ character.password }}</code></div>
            </details>
            <form method="POST" action="{{ url_for('player_logout') }}">
                <button type="submit" class="secondary">Log Out</button>
            </form>
        </div>
    </div>

    <form method="POST" action="{{ url_for('new_post') }}" id="postForm">
        <div class="hint" style="margin-bottom:10px;">Posting as <strong style="color: {{ character.color }};">{{ character.name }}</strong></div>
        <textarea name="message" placeholder="Speak, wretch..." maxlength="{{ max_len }}" required></textarea>
        <div class="char-count">Max {{ max_len }} characters &nbsp;&bull;&nbsp; *bold* &nbsp;&bull;&nbsp; "italic dialogue" &nbsp;&bull;&nbsp; type @ to pick a character</div>

        <div class="dice-roller">
            <h3>&#9860; Dice</h3>
            <div class="dice-grid">
                {% for die in dice_types %}
                <div class="dice-cell">
                    <label for="die-{{ die }}">{{ die }}</label>
                    <input type="number" id="die-{{ die }}" min="0" max="{{ max_dice_per_type }}" value="0">
                </div>
                {% endfor %}
            </div>
            <button type="button" class="secondary" onclick="addRoll()">Add Roll</button>
            <div class="pending-rolls" id="pendingRolls"></div>
        </div>

        <input type="hidden" name="rolls" id="rollsInput" value="[]">
        <label class="whisper-toggle" id="whisperToggle">
            <input type="checkbox" name="whisper_dm" value="1" id="whisperDm">
            Whisper to the DM
        </label>
        <button type="submit" id="postBtn">Post</button>
    </form>

    </div>
    <div class="layout-right">
    <div class="feed-scroll" id="feedScroll">

    {% if posts %}
        {% for post in posts %}
            <div class="card{{ ' whisper-card' if post.is_private else '' }}" data-post-id="{{ post.id }}"
                 data-edit-left="{{ post.edit_seconds_left }}" data-can-delete="{{ 1 if post.can_delete else 0 }}">
                <div class="post-header">
                    {% if post.to_dm %}
                        <span class="whisper-badge">Your whisper to the DM</span>
                    {% elif post.is_private %}
                        <span class="whisper-badge">Whisper just for you</span>
                    {% elif post.is_dm %}
                        <span class="dm-username">DM</span>
                    {% else %}
                        <span class="username" style="color: {{ post.color }};">{{ post.username }}</span>
                    {% endif %}
                    <span class="timestamp">{{ post.timestamp }}{% if post.edited %}<span class="edited-mark">(edited)</span>{% endif %}</span>
                </div>
                <div class="message"{% if post.edit_seconds_left %} data-raw="{{ post.message }}"{% endif %}>{{ post.message | format_message | safe }}</div>
                {% if post.rolls %}
                    <div class="post-rolls">
                        {% for roll in post.rolls %}
                            <span class="roll-badge">
                                {{ roll.label }}: {{ roll.description }} = <span class="roll-total">{{ roll.total }}</span>
                            </span>
                        {% endfor %}
                    </div>
                {% endif %}
            </div>
        {% endfor %}
    {% else %}
        <div class="empty" id="feedEmpty">Silence. Be the first.</div>
    {% endif %}

    </div>
    </div>
    </div>

    <script>
        let CAPACITY = {{ capacity }};
        let MAX_CARRY = {{ capacity * 2 }};
        // Revision of each sheet section this page was built from; sent with
        // every save so a DM change made meanwhile is never overwritten.
        const sheetRevs = {{ character.revs | tojson }};

        function showSheetNotice(text) {
            document.getElementById('sheetNoticeText').textContent = text;
            document.getElementById('sheetNotice').hidden = false;
            if (typeof markTab === 'function') markTab('sheet');
        }

        // --- encumbrance readout ---
        function sectionItems(section) {
            return Array.from(document.querySelectorAll('.inv-input[data-section="' + section + '"]'))
                .map(i => i.value);
        }

        function updateEncumbrance() {
            // Container counts — containers have fixed slots, so they can be
            // full but never overloaded.
            document.querySelectorAll('[data-count-for]').forEach(function (el) {
                const used = sectionItems(el.dataset.countFor).filter(v => v.trim() !== '').length;
                el.textContent = used + ' / ' + el.dataset.capacity + (used >= +el.dataset.capacity ? ' — full' : '');
                el.classList.toggle('full', used >= +el.dataset.capacity);
            });

            // Only what's on your person counts toward Strength + 8.
            const carried = sectionItems('person').filter(v => v.trim() !== '').length;
            const box = document.getElementById('encumbrance');
            box.classList.remove('over', 'impossible');
            if (carried > MAX_CARRY) {
                box.classList.add('impossible');
                box.textContent = 'Carrying ' + carried + ' / ' + CAPACITY +
                    ' — impossible. You cannot carry more than ' + MAX_CARRY + ' items.';
            } else if (carried > CAPACITY) {
                box.classList.add('over');
                box.textContent = 'Carrying ' + carried + ' / ' + CAPACITY +
                    ' — overloaded. DR +2 on Strength and Agility tests.';
            } else {
                box.textContent = 'Carrying ' + carried + ' / ' + CAPACITY + ' items.';
            }
        }

        // --- inventory auto-save ---
        let invSaveTimer = null;
        let invSaving = false;  // a save is queued or in flight
        document.querySelectorAll('.inv-input').forEach(function (input) {
            input.addEventListener('input', function () {
                updateEncumbrance();
                clearTimeout(invSaveTimer);
                document.getElementById('invStatus').textContent = 'Saving...';
                invSaving = true;
                invSaveTimer = setTimeout(saveInventory, 500);
            });
        });

        function flashStatus(ok) {
            document.getElementById('invStatus').textContent = ok ? 'Saved.' : 'Could not save.';
            setTimeout(() => { document.getElementById('invStatus').textContent = ''; }, 2000);
        }

        async function saveInventory() {
            const containers = {};
            document.querySelectorAll('[data-count-for]').forEach(function (el) {
                containers[el.dataset.countFor] = sectionItems(el.dataset.countFor);
            });
            try {
                const resp = await fetch('{{ url_for("update_inventory") }}', {
                    method: 'POST',
                    headers: { 'Content-Type': 'application/json' },
                    body: JSON.stringify({ slots: sectionItems('person'), free: sectionItems('free')[0] || '',
                                           containers: containers, rev: sheetRevs.inventory })
                });
                const data = await resp.json().catch(() => ({}));
                if (resp.status === 409) {
                    document.getElementById('invStatus').textContent = '';
                    showSheetNotice(data.error || 'The DM changed your inventory. Reload to see it.');
                    return;
                }
                if (resp.ok && typeof data.rev === 'number') sheetRevs.inventory = data.rev;
                flashStatus(resp.ok);
            } catch (e) { flashStatus(false); }
            finally { invSaving = false; }
        }

        // --- hp / omens / silver auto-save ---
        let statSaveTimer = null;
        ['hpInput', 'omensInput', 'silverInput'].forEach(function (id) {
            document.getElementById(id).addEventListener('input', function () {
                clearTimeout(statSaveTimer);
                document.getElementById('invStatus').textContent = 'Saving...';
                statSaveTimer = setTimeout(function () { statSaveTimer = null; saveStats(); }, 500);
            });
        });

        async function saveStats() {
            const payload = {
                hp: parseInt(document.getElementById('hpInput').value, 10) || 0,
                omens: parseInt(document.getElementById('omensInput').value, 10) || 0,
                silver: parseInt(document.getElementById('silverInput').value, 10) || 0,
                rev: sheetRevs.vitals
            };
            try {
                const resp = await fetch('{{ url_for("update_stats") }}', {
                    method: 'POST',
                    headers: { 'Content-Type': 'application/json' },
                    body: JSON.stringify(payload)
                });
                if (resp.status === 409) {
                    const data = await resp.json().catch(() => ({}));
                    if (data.sheet) applyVitals(data.sheet);
                    document.getElementById('invStatus').textContent = data.error || 'The DM changed these.';
                    setTimeout(() => { document.getElementById('invStatus').textContent = ''; }, 4000);
                    return;
                }
                flashStatus(resp.ok);
                if (resp.ok) {
                    const data = await resp.json();
                    if (typeof data.rev === 'number') sheetRevs.vitals = data.rev;
                    document.getElementById('brokenBanner').style.display = data.broken ? 'block' : 'none';
                    // Negative HP is death in MÖRK BORG; the server marks the
                    // character dead, so reload into the death screen.
                    if (data.dead) { window.location.reload(); }
                }
            } catch (e) { flashStatus(false); }
        }

        // --- pick up changes the DM makes while this page is open ---
        function applyVitals(sheet) {
            document.getElementById('hpInput').value = sheet.hp;
            document.getElementById('omensInput').value = sheet.omens;
            document.getElementById('silverInput').value = sheet.silver;
            const maxLine = document.getElementById('hpInput').parentElement.querySelector('.stat-sub');
            if (maxLine) maxLine.textContent = 'max ' + sheet.max_hp;
            document.getElementById('brokenBanner').style.display = sheet.hp === 0 ? 'block' : 'none';
            sheetRevs.vitals = sheet.revs.vitals;
            markTab('sheet');
        }

        // Abilities, conditions, capacity and the stat-roll dropdown all
        // follow the DM live — no reload needed.
        function signedText(n) { return n >= 0 ? '+' + n : String(n); }

        function applyAbilities(sheet) {
            Object.keys(sheet.abilities).forEach(function (key) {
                const box = document.getElementById('ability-' + key);
                if (!box) return;
                const eff = sheet.abilities[key], base = sheet.base_abilities[key];
                box.querySelector('.stat-value').textContent = signedText(eff);
                box.querySelector('.stat-sub').textContent = eff !== base ? 'base ' + signedText(base) : '';
                box.classList.toggle('conditioned', eff !== base);
                const stat = rollStats.find(s => s[0] === key);
                if (stat) stat[2] = eff;
            });

            const list = document.getElementById('conditionsList');
            list.replaceChildren(...sheet.conditions.map(function (c) {
                const pill = document.createElement('span');
                pill.className = 'condition-pill';
                const name = document.createElement('b');
                name.textContent = c.name;
                pill.appendChild(name);
                if (c.summary) pill.appendChild(document.createTextNode(' ' + c.summary));
                return pill;
            }));
            document.getElementById('conditionsBox').hidden = sheet.conditions.length === 0;

            CAPACITY = sheet.capacity;
            MAX_CARRY = sheet.capacity * 2;
            document.getElementById('capacityLabel').textContent = sheet.capacity;
            updateEncumbrance();
            renderPendingRolls();
            sheetRevs.abilities = sheet.revs.abilities;
            sheetRevs.conditions = sheet.revs.conditions;
            markTab('sheet');
        }

        function handleSheet(sheet) {
            if (!sheet) return;
            if (sheet.dead) { window.location.reload(); return; }
            if (sheet.revs.abilities !== sheetRevs.abilities || sheet.revs.conditions !== sheetRevs.conditions) {
                applyAbilities(sheet);
            }
            // HP / omens / silver update in place — unless the player is
            // mid-edit, in which case their save comes back 409 with the
            // latest values anyway.
            if (sheet.revs.vitals !== sheetRevs.vitals && !statSaveTimer) applyVitals(sheet);
            const other = ['kit', 'inventory']
                .filter(k => sheet.revs[k] !== sheetRevs[k] && !(k === 'inventory' && invSaving));
            if (other.length) showSheetNotice('The DM changed your ' + other.join(' and ') + '. Reload to see it.');
        }

        // --- dice roller (posts) ---
        const diceTypes = {{ dice_types | tojson }};
        // [key, label, modifier] for each ability — display only; the server
        // re-reads the modifier from the character sheet when the post lands.
        const rollStats = [
            {% for key, label in ability_pairs %}[{{ key | tojson }}, {{ label | tojson }}, {{ effective[key] | int }}],{% endfor %}
        ];
        let pendingRolls = [];

        function signedNum(n) { return n >= 0 ? '+' + n : String(n); }

        function rollStat(roll) {
            return rollStats.find(function (s) { return s[0] === roll.ability; }) || null;
        }
        let rollCounter = 1;

        function updateRollsInput() {
            document.getElementById('rollsInput').value = JSON.stringify(pendingRolls);
        }

        function renderPendingRolls() {
            const container = document.getElementById('pendingRolls');
            container.innerHTML = '';
            pendingRolls.forEach((roll, index) => {
                const div = document.createElement('div');
                div.className = 'roll-item';

                const labelInput = document.createElement('input');
                labelInput.type = 'text';
                labelInput.className = 'roll-label-input';
                labelInput.maxLength = {{ max_roll_label_len }};
                labelInput.value = roll.label;
                labelInput.placeholder = 'Label';
                labelInput.addEventListener('input', function () {
                    pendingRolls[index].label = this.value;
                    updateRollsInput();
                });

                const statSelect = document.createElement('select');
                statSelect.className = 'roll-stat-select';
                statSelect.title = 'Add one of your abilities to this roll';
                const none = document.createElement('option');
                none.value = '';
                none.textContent = 'No stat';
                statSelect.appendChild(none);
                rollStats.forEach(function (s) {
                    const opt = document.createElement('option');
                    opt.value = s[0];
                    opt.textContent = s[1] + ' ' + signedNum(s[2]);
                    statSelect.appendChild(opt);
                });
                statSelect.value = roll.ability || '';

                const desc = document.createElement('span');
                desc.className = 'roll-desc';
                function renderDesc() {
                    const stat = rollStat(roll);
                    if (stat) {
                        desc.innerHTML = roll.description + ' + ' + stat[1] + ' (' + signedNum(stat[2]) +
                            ') = <strong>' + (roll.total + stat[2]) + '</strong>';
                    } else {
                        desc.innerHTML = roll.description + ' = <strong>' + roll.total + '</strong>';
                    }
                }
                renderDesc();

                statSelect.addEventListener('change', function () {
                    const oldStat = rollStat(roll);
                    roll.ability = this.value || null;
                    const newStat = rollStat(roll);
                    // Retitle the roll to the stat unless the player already typed their own label.
                    const autoLabel = /^Roll [0-9]+$/.test(roll.label) || (oldStat && roll.label === oldStat[1]);
                    if (autoLabel) {
                        roll.label = newStat ? newStat[1] : 'Roll ' + (index + 1);
                        labelInput.value = roll.label;
                    }
                    renderDesc();
                    updateRollsInput();
                });

                const btn = document.createElement('button');
                btn.type = 'button';
                btn.className = 'remove-btn';
                btn.textContent = 'Remove';
                btn.onclick = function () { removeRoll(index); };

                div.appendChild(labelInput);
                div.appendChild(statSelect);
                div.appendChild(desc);
                div.appendChild(btn);
                container.appendChild(div);
            });
        }

        function removeRoll(index) {
            pendingRolls.splice(index, 1);
            renderPendingRolls();
            updateRollsInput();
        }

        async function addRoll() {
            const dice = {};
            let hasAny = false;
            diceTypes.forEach(function (die) {
                const val = parseInt(document.getElementById('die-' + die).value, 10) || 0;
                if (val > 0) { dice[die] = val; hasAny = true; }
            });
            if (!hasAny) { alert('Set a quantity for at least one die before adding a roll.'); return; }
            if (pendingRolls.length >= {{ max_rolls_per_post }}) { alert('Maximum of {{ max_rolls_per_post }} rolls per post.'); return; }

            try {
                const resp = await fetch('{{ url_for("roll_dice") }}', {
                    method: 'POST',
                    headers: { 'Content-Type': 'application/json' },
                    body: JSON.stringify({ dice: dice })
                });
                if (!resp.ok) { const err = await resp.json(); alert(err.error || 'Roll failed.'); return; }
                const data = await resp.json();
                data.label = 'Roll ' + rollCounter++;
                data.ability = null;
                pendingRolls.push(data);
                renderPendingRolls();
                updateRollsInput();
                diceTypes.forEach(function (die) { document.getElementById('die-' + die).value = 0; });
            } catch (e) {
                alert('Could not reach the server to roll dice.');
            }
        }

        // --- whisper-to-DM toggle ---
        (function () {
            const box = document.getElementById('whisperDm');
            const form = document.getElementById('postForm');
            const label = document.getElementById('whisperToggle');
            const btn = document.getElementById('postBtn');
            box.addEventListener('change', function () {
                form.classList.toggle('whispering', box.checked);
                label.classList.toggle('on', box.checked);
                btn.textContent = box.checked ? 'Whisper to DM' : 'Post';
                btn.classList.toggle('whisper-btn', box.checked);
            });
        })();

        // --- live feed polling ---
        let lastSeq = {{ latest_seq }};
        let lastChange = {{ latest_change }};
        let currentSceneName = {{ scene_name | tojson }};

        function buildRollsHtml(rolls) {
            if (!rolls || !rolls.length) return '';
            let html = '<div class="post-rolls">';
            rolls.forEach(function (roll) {
                html += '<span class="roll-badge">' + roll.label + ': ' + roll.description +
                    ' = <span class="roll-total">' + roll.total + '</span></span>';
            });
            html += '</div>';
            return html;
        }

        function buildPostCard(post) {
            const div = document.createElement('div');
            div.className = 'card' + (post.is_private ? ' whisper-card' : '');
            div.dataset.postId = post.id;

            let header;
            if (post.to_dm) {
                header = '<span class="whisper-badge">Your whisper to the DM</span>';
            } else if (post.is_private) {
                header = '<span class="whisper-badge">Whisper just for you</span>';
            } else if (post.is_dm) {
                header = '<span class="dm-username">DM</span>';
            } else {
                header = '<span class="username" style="color:' + post.color + ';">' + post.username + '</span>';
            }

            div.innerHTML =
                '<div class="post-header">' + header +
                '<span class="timestamp">' + post.timestamp +
                (post.edited ? '<span class="edited-mark">(edited)</span>' : '') + '</span></div>' +
                '<div class="message">' + post.message_html + '</div>' +
                buildRollsHtml(post.rolls);
            if (typeof post.message_raw === 'string') div.querySelector('.message').dataset.raw = post.message_raw;
            div.dataset.editLeft = post.edit_seconds_left || 0;
            div.dataset.canDelete = post.can_delete ? 1 : 0;
            addOwnControls(div);

            return div;
        }

        // --- phone tabs: Feed (default) / Sheet ---
        let activeTab = 'feed';
        function phoneLayout() { return window.matchMedia('(max-width: 850px)').matches; }

        function setTab(name) {
            activeTab = name;
            document.body.classList.toggle('tab-feed', name === 'feed');
            document.body.classList.toggle('tab-sheet', name === 'sheet');
            document.querySelectorAll('.mobile-tabs button').forEach(function (b) {
                const on = b.dataset.tab === name;
                b.classList.toggle('active', on);
                b.setAttribute('aria-selected', on ? 'true' : 'false');
                if (on) b.querySelector('.tab-dot').hidden = true;
            });
            try { sessionStorage.setItem('morkborgTab', name); } catch (e) { /* private mode */ }
        }

        // Dot on the other tab when something arrives there unseen.
        function markTab(name) {
            if (!phoneLayout() || activeTab === name) return;
            const dot = document.querySelector('.mobile-tabs button[data-tab="' + name + '"] .tab-dot');
            if (dot) dot.hidden = false;
        }

        document.querySelectorAll('.mobile-tabs button').forEach(function (b) {
            b.addEventListener('click', function () { setTab(b.dataset.tab); window.scrollTo(0, 0); });
        });
        (function () {
            let saved = null;
            try { saved = sessionStorage.getItem('morkborgTab'); } catch (e) { /* private mode */ }
            setTab(saved === 'sheet' ? 'sheet' : 'feed');
        })();

        // --- edit / delete your own recent posts ---
        const EDIT_URL = '{{ url_for("edit_own_post", post_id="__ID__") }}';
        const DELETE_URL = '{{ url_for("delete_own_post", post_id="__ID__") }}';
        const MAX_POST_LEN = {{ max_len }};

        // The server says how many seconds are left; turn that into a local
        // deadline so a wrong clock on this device doesn't matter.
        function addOwnControls(card) {
            const left = parseInt(card.dataset.editLeft || '0', 10);
            if (!(left > 0)) return;
            card.dataset.deadline = Date.now() + left * 1000;
            const header = card.querySelector('.post-header');
            const actions = document.createElement('span');
            actions.className = 'own-actions';
            const edit = document.createElement('button');
            edit.type = 'button';
            edit.className = 'secondary';
            edit.textContent = 'Edit';
            edit.addEventListener('click', () => startEdit(card));
            actions.appendChild(edit);
            if (card.dataset.canDelete === '1') {
                const del = document.createElement('button');
                del.type = 'button';
                del.className = 'delete-post-btn';
                del.textContent = 'Delete';
                del.addEventListener('click', () => deleteOwnPost(card));
                actions.appendChild(del);
            }
            header.insertBefore(actions, header.querySelector('.timestamp'));
        }

        function expireOwnControls() {
            document.querySelectorAll('[data-deadline]').forEach(function (card) {
                if (Date.now() < +card.dataset.deadline) return;
                const actions = card.querySelector('.own-actions');
                if (actions) actions.remove();
                const editor = card.querySelector('.post-edit');
                if (editor) {
                    // Window closed mid-edit: the save would be refused, so say so.
                    const err = editor.querySelector('.post-edit-error');
                    err.textContent = 'The edit window has closed.';
                    editor.querySelector('.post-edit-save').disabled = true;
                }
                delete card.dataset.deadline;
            });
        }

        function startEdit(card) {
            if (card.querySelector('.post-edit')) return;
            const messageEl = card.querySelector('.message');
            const editor = document.createElement('div');
            editor.className = 'post-edit';
            const box = document.createElement('textarea');
            box.maxLength = MAX_POST_LEN;
            box.value = messageEl.dataset.raw || messageEl.textContent;
            const bar = document.createElement('div');
            bar.className = 'post-edit-bar';
            const save = document.createElement('button');
            save.type = 'button';
            save.className = 'post-edit-save';
            save.textContent = 'Save';
            const cancel = document.createElement('button');
            cancel.type = 'button';
            cancel.className = 'secondary';
            cancel.textContent = 'Cancel';
            const err = document.createElement('span');
            err.className = 'post-edit-error';
            bar.append(save, cancel, err);
            editor.append(box, bar);
            messageEl.hidden = true;
            messageEl.after(editor);
            box.focus();

            cancel.addEventListener('click', function () { editor.remove(); messageEl.hidden = false; });
            save.addEventListener('click', async function () {
                save.disabled = true;
                err.textContent = '';
                try {
                    const resp = await fetch(EDIT_URL.replace('__ID__', encodeURIComponent(card.dataset.postId)), {
                        method: 'POST',
                        headers: { 'Content-Type': 'application/json' },
                        body: JSON.stringify({ message: box.value })
                    });
                    const data = await resp.json().catch(() => ({}));
                    if (resp.ok && data.post) {
                        card.replaceWith(buildPostCard(data.post));
                    } else {
                        err.textContent = data.error || 'Could not save.';
                        save.disabled = false;
                    }
                } catch (e) {
                    err.textContent = 'Could not save.';
                    save.disabled = false;
                }
            });
        }

        async function deleteOwnPost(card) {
            if (!confirm('Delete this post?')) return;
            try {
                const resp = await fetch(DELETE_URL.replace('__ID__', encodeURIComponent(card.dataset.postId)), {
                    method: 'POST',
                    headers: { 'Content-Type': 'application/json' },
                    body: '{}'
                });
                const data = await resp.json().catch(() => ({}));
                if (resp.ok) card.remove();
                else alert(data.error || 'Could not delete.');
            } catch (e) { alert('Could not delete.'); }
        }

        document.querySelectorAll('#feedScroll [data-edit-left]').forEach(addOwnControls);
        setInterval(expireOwnControls, 5000);

        async function pollFeed() {
            try {
                const resp = await fetch('{{ url_for("api_feed") }}?sheet=1&after_seq=' + lastSeq +
                                         '&after_change=' + lastChange);
                if (!resp.ok) return;
                const data = await resp.json();
                handleSheet(data.sheet);
                applyFeedChanges(data, buildPostCard);
                if (typeof data.latest_change === 'number') lastChange = data.latest_change;

                if (data.posts && data.posts.length) {
                    const container = document.getElementById('feedScroll');
                    const empty = document.getElementById('feedEmpty');
                    if (empty) empty.remove();
                    data.posts.forEach(function (post) {
                        container.insertBefore(buildPostCard(post), container.firstChild);
                    });
                    markTab('feed');
                }
                if (typeof data.latest_seq === 'number') lastSeq = data.latest_seq;

                if (data.scene_name && data.scene_name !== currentSceneName) {
                    currentSceneName = data.scene_name;
                    document.title = currentSceneName;
                    const h1 = document.querySelector('.topbar h1');
                    if (h1) h1.textContent = currentSceneName;
                }
            } catch (e) {
                // Silent — the next interval just tries again.
            }
        }

        updateEncumbrance();
        setInterval(pollFeed, 4000);
    </script>
""" + MENTION_SCRIPT + """
</body>
</html>
"""

BOARD_TEMPLATE = (
    BOARD_TEMPLATE
    .replace('__MIN_HP__', str(MIN_HP))
    .replace('__MAX_HP__', str(MAX_HP))
    .replace('__MAX_SILVER__', str(MAX_SILVER))
)


# ---------------------------------------------------------------------------
# TEMPLATE: death screen
# ---------------------------------------------------------------------------
DEATH_TEMPLATE = """
<!doctype html>
<html lang="en">
<head>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <title>Dead</title>
""" + FAVICON + SHARED_CSS + POPOUT_SCRIPT + """
</head>
<body>
""" + TOP_BAR + """
    {% with messages = get_flashed_messages() %}
        {% if messages %}
            {% for m in messages %}<div class="flash">{{ m }}</div>{% endfor %}
        {% endif %}
    {% endwith %}
    <div class="card death-card">
        <div class="skull">&#128128;</div>
        <h2>{{ character.name }} is dead</h2>
        <p class="hint">The dying world takes another. Roll up something new &mdash; it won't last either.</p>
        <form method="POST" action="{{ url_for('retire_character') }}" style="background:none; border:none;">
            <button type="submit">Create a New Scvm</button>
        </form>
    </div>
</body>
</html>
"""

DM_LOGIN_TEMPLATE = """
<!doctype html>
<html lang="en">
<head>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <title>DM</title>
""" + FAVICON + SHARED_CSS + POPOUT_SCRIPT + """
</head>
<body>
""" + TOP_BAR + """
    {% with messages = get_flashed_messages() %}
        {% if messages %}
            {% for m in messages %}<div class="flash">{{ m }}</div>{% endfor %}
        {% endif %}
    {% endwith %}
    <div class="card">
        <h2>DM Access</h2>
        <div class="h-under"></div>
        <form method="POST" action="{{ url_for('dm_login') }}">
            <input type="password" name="password" placeholder="DM password" required>
            <button type="submit">Enter</button>
        </form>
    </div>
</body>
</html>
"""


# ---------------------------------------------------------------------------
# TEMPLATE: DM dashboard
# ---------------------------------------------------------------------------
DM_DASHBOARD_TEMPLATE = """
<!doctype html>
<html lang="en">
<head>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <title>DM &mdash; {{ scene_name }}</title>
""" + FAVICON + SHARED_CSS + POPOUT_SCRIPT + """
</head>
<body>
""" + TOP_BAR + """
    {% with messages = get_flashed_messages() %}
        {% if messages %}
            {% for m in messages %}<div class="flash">{{ m }}</div>{% endfor %}
        {% endif %}
    {% endwith %}

    <nav class="mobile-tabs" role="tablist" aria-label="Dashboard">
        <button type="button" role="tab" data-tab="feed">Feed<span class="tab-dot" hidden></span></button>
        <button type="button" role="tab" data-tab="table">Table<span class="tab-dot" hidden></span></button>
    </nav>
    <div class="layout">
    <div class="layout-left">

    <div class="card dm-table-card">
        <h2>DM Dashboard</h2>
        <div class="h-under"></div>
        <p class="hint">
            {{ characters|length }} character(s) created.
            <a href="{{ url_for('dm_logout') }}">Log out</a> &nbsp;&bull;&nbsp;
            <a href="{{ url_for('dm_backup') }}">Download backup</a>
        </p>
    </div>

    <div class="card docs-card dm-table-card">
        <h3>Table Documents</h3>
        <div class="shelf">
            {% for adv in adventures %}
                {% if adv.available %}
                    <a class="shelf-btn" href="{{ url_for('adventure', slug=adv.slug) }}" target="_blank" rel="noopener noreferrer"
                       onclick="return popout(this.href, 'adv_{{ adv.slug }}', 1000, 1000);">&#9670; {{ adv.title }}</a>
                {% else %}
                    <span class="shelf-btn pending" title="Drop the file into the adventures folder to enable this">
                        &#9671; {{ adv.title }} &mdash; not added yet</span>
                {% endif %}
            {% else %}
                <span class="hint">No adventures added.</span>
            {% endfor %}
        </div>
    </div>

    <div class="card" id="dmPostCard">
        <h3>Post as DM</h3>
        <form method="POST" action="{{ url_for('dm_post') }}" id="dmPostForm" style="background:none; border:none; padding:0;">
            <label class="post-target">
                <span>To</span>
                <select name="whisper_to" id="dmWhisperTo">
                    <option value="">Everyone &mdash; general post</option>
                    {% for character in characters if not character.dead %}
                        <option value="{{ character.id }}">Whisper: {{ character.name }}{% if character.class_name %} &mdash; {{ character.class_name }}{% endif %}</option>
                    {% endfor %}
                </select>
            </label>
            <textarea name="message" placeholder="..." required></textarea>
            <div class="char-count">*bold* &nbsp;&bull;&nbsp; "italic dialogue" &nbsp;&bull;&nbsp; type @ to pick a character</div>
            <div class="dice-roller">
                <h3>&#9860; Dice</h3>
                <div class="dice-grid">
                    {% for die in dice_types %}
                    <div class="dice-cell">
                        <label for="dm-die-{{ die }}">{{ die }}</label>
                        <input type="number" id="dm-die-{{ die }}" min="0" max="{{ max_dice_per_type }}" value="0">
                    </div>
                    {% endfor %}
                    <div class="dice-cell">
                        <label for="dm-die-mod">Mod</label>
                        <input type="number" id="dm-die-mod" min="-{{ max_roll_modifier }}" max="{{ max_roll_modifier }}" step="1" value="0">
                    </div>
                </div>
                <button type="button" class="secondary" onclick="dmAddRoll()">Add Roll</button>
                <div class="pending-rolls" id="dmPendingRolls"></div>
            </div>
            <input type="hidden" name="rolls" id="dmRollsInput" value="[]">
            <button type="submit" id="dmPostBtn">Post as DM</button>
        </form>
    </div>
    <div class="card dm-table-card">
        <h3>Current Scene</h3>
        <p class="hint">Shown as the page title and banner for every player.</p>
        <form method="POST" action="{{ url_for('dm_set_scene') }}" style="background:none; border:none; padding:0;">
            <input type="text" name="scene_name" value="{{ scene_name }}" maxlength="__MAX_SCENE_LENGTH__"
                   placeholder="e.g. The Valley of the Unfortunate Undead" required>
            <button type="submit" class="secondary">Set Scene</button>
        </form>
    </div>


    </div>
    <div class="layout-right">
    <h2>Messages</h2>
    <div class="h-under"></div>
    <div class="feed-scroll" id="feedScroll">

    {% for post in posts %}
        <div class="card{{ ' whisper-card' if post.is_private else '' }}" data-post-id="{{ post.id }}">
            <div class="post-header">
                <span class="post-header-left">
                    {% if post.to_dm %}
                        <span class="whisper-badge">Whisper to DM from</span>
                        <span class="username" style="color: {{ post.color }};">{{ post.username }}</span>
                    {% elif post.is_private %}
                        <span class="whisper-badge">Whisper to {{ post.target_character_name }}</span>
                    {% elif post.is_dm %}
                        <span class="dm-username">DM</span>
                    {% else %}
                        <span class="username" style="color: {{ post.color }};">{{ post.username }}</span>
                    {% endif %}
                    <form method="POST" action="{{ url_for('dm_delete_post') }}" class="delete-post-form"
                          onsubmit="return confirm('Delete this message?');">
                        <input type="hidden" name="post_id" value="{{ post.id }}">
                        <button type="submit" class="delete-post-btn">Delete</button>
                    </form>
                </span>
                <span class="timestamp">{{ post.timestamp }}{% if post.edited %}<span class="edited-mark">(edited)</span>{% endif %}</span>
            </div>
            <div class="message">{{ post.message | format_message | safe }}</div>
            {% if post.rolls %}
                <div class="post-rolls">
                    {% for roll in post.rolls %}
                        <span class="roll-badge">
                            {{ roll.label }}: {{ roll.description }} = <span class="roll-total">{{ roll.total }}</span>
                        </span>
                    {% endfor %}
                </div>
            {% endif %}
        </div>
    {% else %}
        <div class="empty" id="feedEmpty">No messages yet.</div>
    {% endfor %}

    </div>
    </div>
    </div>

    <script>
        const dmDiceTypes = {{ dice_types | tojson }};

        // The DM page has two independent dice widgets (announcements and
        // whispers). makeRoller() builds one bound to a given id prefix so
        // the logic isn't duplicated once per widget.
        function makeRoller(prefix, pendingId, inputId) {
            let pending = [];
            let counter = 1;

            function syncInput() {
                document.getElementById(inputId).value = JSON.stringify(pending);
            }

            function render() {
                const container = document.getElementById(pendingId);
                container.innerHTML = '';
                pending.forEach((roll, index) => {
                    const div = document.createElement('div');
                    div.className = 'roll-item';

                    const labelInput = document.createElement('input');
                    labelInput.type = 'text';
                    labelInput.className = 'roll-label-input';
                    labelInput.maxLength = {{ max_roll_label_len }};
                    labelInput.value = roll.label;
                    labelInput.placeholder = 'Label';
                    labelInput.addEventListener('input', function () {
                        pending[index].label = this.value;
                        syncInput();
                    });

                    const desc = document.createElement('span');
                    desc.className = 'roll-desc';
                    const mod = roll.modifier || 0;
                    // A 0 modifier adds nothing, so unmodified rolls don't say "+ 0".
                    const modText = mod > 0 ? ' + ' + mod : mod < 0 ? ' - ' + (-mod) : '';
                    desc.innerHTML = roll.description + modText + ' = <strong>' + (roll.total + mod) + '</strong>';

                    const btn = document.createElement('button');
                    btn.type = 'button';
                    btn.className = 'remove-btn';
                    btn.textContent = 'Remove';
                    btn.onclick = function () { pending.splice(index, 1); render(); syncInput(); };

                    div.appendChild(labelInput);
                    div.appendChild(desc);
                    div.appendChild(btn);
                    container.appendChild(div);
                });
            }

            return async function add() {
                const dice = {};
                let hasAny = false;
                dmDiceTypes.forEach(function (die) {
                    const val = parseInt(document.getElementById(prefix + die).value, 10) || 0;
                    if (val > 0) { dice[die] = val; hasAny = true; }
                });
                if (!hasAny) { alert('Set a quantity for at least one die before adding a roll.'); return; }
                let modifier = parseInt(document.getElementById(prefix + 'mod').value, 10) || 0;
                modifier = Math.max(-{{ max_roll_modifier }}, Math.min({{ max_roll_modifier }}, modifier));
                if (pending.length >= {{ max_rolls_per_post }}) { alert('Maximum of {{ max_rolls_per_post }} rolls per post.'); return; }

                try {
                    const resp = await fetch('{{ url_for("roll_dice") }}', {
                        method: 'POST',
                        headers: { 'Content-Type': 'application/json' },
                        body: JSON.stringify({ dice: dice })
                    });
                    if (!resp.ok) { const err = await resp.json(); alert(err.error || 'Roll failed.'); return; }
                    const data = await resp.json();
                    data.label = 'Roll ' + counter++;
                    data.modifier = modifier;
                    pending.push(data);
                    render();
                    syncInput();
                    dmDiceTypes.forEach(function (die) { document.getElementById(prefix + die).value = 0; });
                    document.getElementById(prefix + 'mod').value = 0;
                } catch (e) {
                    alert('Could not reach the server to roll dice.');
                }
            };
        }

        const dmAddRoll = makeRoller('dm-die-', 'dmPendingRolls', 'dmRollsInput');

        // --- who the post goes to: everyone, or a whisper to one character ---
        (function () {
            const select = document.getElementById('dmWhisperTo');
            const card = document.getElementById('dmPostCard');
            const btn = document.getElementById('dmPostBtn');
            function styleForTarget() {
                const opt = select.options[select.selectedIndex];
                const whisper = !!select.value;
                card.classList.toggle('whispering', whisper);
                btn.classList.toggle('whisper-btn', whisper);
                btn.textContent = whisper ? 'Whisper to ' + opt.dataset.name : 'Post as DM';
            }
            Array.from(select.options).forEach(function (o) {
                if (o.value) o.dataset.name = o.textContent.replace(/^Whisper: /, '').split(' \u2014 ')[0];
            });
            select.addEventListener('change', styleForTarget);

            // Refresh the list when it's opened, so characters created after
            // this page loaded can be whispered to without a reload.
            let lastFetch = 0;
            async function refreshTargets() {
                if (Date.now() - lastFetch < 10000) return;
                lastFetch = Date.now();
                try {
                    const resp = await fetch('{{ url_for("dm_players_state") }}');
                    if (!resp.ok) return;
                    const living = (await resp.json()).characters.filter(c => !c.dead);
                    const keep = select.value;
                    const everyone = select.options[0];
                    select.replaceChildren(everyone, ...living.map(function (c) {
                        const o = document.createElement('option');
                        o.value = c.id;
                        o.dataset.name = c.name;
                        o.textContent = 'Whisper: ' + c.name + (c.class_name ? ' \u2014 ' + c.class_name : '');
                        return o;
                    }));
                    select.value = living.some(c => c.id === keep) ? keep : '';
                    styleForTarget();
                } catch (e) { /* keep the current list */ }
            }
            select.addEventListener('focus', refreshTargets);
            select.addEventListener('pointerdown', refreshTargets);
            styleForTarget();
        })();

        // --- phone tabs: Feed (default) / Table ---
        let dmActiveTab = 'feed';
        function dmSetTab(name) {
            dmActiveTab = name;
            document.body.classList.toggle('tab-feed', name === 'feed');
            document.body.classList.toggle('tab-table', name === 'table');
            document.querySelectorAll('.mobile-tabs button').forEach(function (b) {
                const on = b.dataset.tab === name;
                b.classList.toggle('active', on);
                b.setAttribute('aria-selected', on ? 'true' : 'false');
                if (on) b.querySelector('.tab-dot').hidden = true;
            });
            try { sessionStorage.setItem('morkborgDmTab', name); } catch (e) { /* private mode */ }
        }
        function dmMarkFeed() {
            if (dmActiveTab === 'feed' || !window.matchMedia('(max-width: 850px)').matches) return;
            document.querySelector('.mobile-tabs button[data-tab="feed"] .tab-dot').hidden = false;
        }
        document.querySelectorAll('.mobile-tabs button').forEach(function (b) {
            b.addEventListener('click', function () { dmSetTab(b.dataset.tab); window.scrollTo(0, 0); });
        });
        (function () {
            let saved = null;
            try { saved = sessionStorage.getItem('morkborgDmTab'); } catch (e) { /* private mode */ }
            dmSetTab(saved === 'table' ? 'table' : 'feed');
        })();

        // --- live feed polling ---
        let dmLastSeq = {{ latest_seq }};
        let dmLastChange = {{ latest_change }};
        let dmCurrentSceneName = {{ scene_name | tojson }};

        function dmBuildRollsHtml(rolls) {
            if (!rolls || !rolls.length) return '';
            let html = '<div class="post-rolls">';
            rolls.forEach(function (roll) {
                html += '<span class="roll-badge">' + roll.label + ': ' + roll.description +
                    ' = <span class="roll-total">' + roll.total + '</span></span>';
            });
            html += '</div>';
            return html;
        }

        function dmBuildPostCard(post) {
            const div = document.createElement('div');
            div.className = 'card' + (post.is_private ? ' whisper-card' : '');
            div.dataset.postId = post.id;

            let badge;
            if (post.to_dm) {
                badge = '<span class="whisper-badge">Whisper to DM from</span> ' +
                    '<span class="username" style="color:' + post.color + ';">' + post.username + '</span>';
            } else if (post.is_private) {
                badge = '<span class="whisper-badge">Whisper to ' + post.target_character_name + '</span>';
            } else if (post.is_dm) {
                badge = '<span class="dm-username">DM</span>';
            } else {
                badge = '<span class="username" style="color:' + post.color + ';">' + post.username + '</span>';
            }

            const deleteForm = document.createElement('form');
            deleteForm.method = 'POST';
            deleteForm.action = '{{ url_for("dm_delete_post") }}';
            deleteForm.className = 'delete-post-form';
            deleteForm.onsubmit = function () { return confirm('Delete this message?'); };
            deleteForm.innerHTML =
                '<input type="hidden" name="post_id" value="' + post.id + '">' +
                '<button type="submit" class="delete-post-btn">Delete</button>';

            const headerLeft = document.createElement('span');
            headerLeft.className = 'post-header-left';
            headerLeft.innerHTML = badge;
            headerLeft.appendChild(deleteForm);

            const header = document.createElement('div');
            header.className = 'post-header';
            header.appendChild(headerLeft);
            const timestamp = document.createElement('span');
            timestamp.className = 'timestamp';
            timestamp.textContent = post.timestamp;
            if (post.edited) {
                const mark = document.createElement('span');
                mark.className = 'edited-mark';
                mark.textContent = '(edited)';
                timestamp.appendChild(mark);
            }
            header.appendChild(timestamp);

            div.appendChild(header);

            const messageDiv = document.createElement('div');
            messageDiv.className = 'message';
            messageDiv.innerHTML = post.message_html;
            div.appendChild(messageDiv);

            const rollsHtml = dmBuildRollsHtml(post.rolls);
            if (rollsHtml) {
                const wrapper = document.createElement('div');
                wrapper.innerHTML = rollsHtml;
                div.appendChild(wrapper.firstChild);
            }

            return div;
        }

        async function dmPollFeed() {
            try {
                const resp = await fetch('{{ url_for("api_feed") }}?after_seq=' + dmLastSeq +
                                         '&after_change=' + dmLastChange);
                if (!resp.ok) return;
                const data = await resp.json();
                applyFeedChanges(data, dmBuildPostCard);
                if (typeof data.latest_change === 'number') dmLastChange = data.latest_change;

                if (data.posts && data.posts.length) {
                    const container = document.getElementById('feedScroll');
                    const empty = document.getElementById('feedEmpty');
                    if (empty) empty.remove();
                    data.posts.forEach(function (post) {
                        container.insertBefore(dmBuildPostCard(post), container.firstChild);
                    });
                    dmMarkFeed();
                }
                if (typeof data.latest_seq === 'number') dmLastSeq = data.latest_seq;

                if (data.scene_name && data.scene_name !== dmCurrentSceneName) {
                    dmCurrentSceneName = data.scene_name;
                    const h1 = document.querySelector('.topbar h1');
                    if (h1) h1.textContent = dmCurrentSceneName;
                }
            } catch (e) {
                // Silent — the next interval just tries again.
            }
        }

        setInterval(dmPollFeed, 4000);
    </script>
""" + MENTION_SCRIPT + """
</body>
</html>
"""

DM_DASHBOARD_TEMPLATE = (
    DM_DASHBOARD_TEMPLATE
    .replace('__MAX_SCENE_LENGTH__', str(MAX_SCENE_LENGTH))
    .replace('__MIN_ABILITY__', str(MIN_ABILITY))
    .replace('__MAX_ABILITY__', str(MAX_ABILITY))
    .replace('__MIN_HP__', str(MIN_HP))
    .replace('__MAX_HP__', str(MAX_HP))
    .replace('__MAX_SILVER__', str(MAX_SILVER))
)


# ---------------------------------------------------------------------------
# TEMPLATE: DM Players pop-out — roster, or one character's editor
# ---------------------------------------------------------------------------
DM_PLAYERS_TEMPLATE = """
<!doctype html>
<html lang="en">
<head>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <title>{% if character %}{{ character.name }} &mdash; {% endif %}Players</title>
""" + FAVICON + SHARED_CSS + """
<style>
    body { max-width: 860px; }
    .players-head { display: flex; align-items: baseline; justify-content: space-between; gap: 12px; margin: 6px 0 14px; }
    .players-head h2 { margin: 0; }
    .players-head a { color: var(--acid); font-weight: 900; text-transform: uppercase; letter-spacing: .1em; text-decoration: none; }
    .roster-row {
        display: grid; grid-template-columns: minmax(130px, 1.6fr) auto auto minmax(120px, 1fr);
        gap: 12px; align-items: center; padding: 10px 12px; margin-bottom: 8px;
        background: var(--panel, #141217); border-left: 6px solid var(--acid);
    }
    .roster-row.dead { border-left-color: var(--ash); opacity: .7; grid-template-columns: 1fr auto; }
    .roster-name { cursor: pointer; min-width: 0; }
    .roster-name b { font-size: 1.15em; }
    .roster-name:hover b { text-decoration: underline; }
    .roster-name .sub { display: block; font-size: .78em; color: var(--ash); text-transform: uppercase; letter-spacing: .08em; }
    .roster-badge { display: inline-block; margin: 3px 4px 0 0; padding: 1px 6px; font-size: .68em; font-weight: 900;
                    letter-spacing: .1em; text-transform: uppercase; background: var(--rot); color: var(--ink); }
    .roster-badge.warn { background: var(--acid); }
    .roster-badge.cond { background: transparent; color: var(--rot); border: 1px solid var(--rot); }
    .nudge { display: flex; align-items: center; gap: 4px; white-space: nowrap; }
    .nudge .k { font-size: .7em; color: var(--ash); text-transform: uppercase; letter-spacing: .1em; margin-right: 2px; }
    .nudge .v { min-width: 3.2em; text-align: center; font-weight: 900; font-size: 1.1em; }
    .nudge button { margin: 0; padding: 2px 9px; font-size: 1em; line-height: 1.2; }
    .roster-load { font-size: .82em; color: var(--ash); text-align: right; }
    .roster-load b { color: var(--bone); }
    .roster-open { margin: 0; padding: 4px 12px; font-size: .85em; }
    details.graveyard summary { cursor: pointer; margin: 18px 0 10px; color: var(--ash); font-weight: 900;
                                text-transform: uppercase; letter-spacing: .12em; }
    .stale-notice { display: flex; align-items: center; justify-content: space-between; gap: 10px; }
    .stale-notice button { margin: 0; }
    @media (max-width: 620px) {
        .roster-row { grid-template-columns: 1fr 1fr; }
        .roster-name, .roster-load { grid-column: 1 / -1; text-align: left; }
    }
</style>
</head>
<body>
    <div class="players-head">
        <h2>{% if character %}<span style="color: {{ character.color }};">{{ character.name }}</span>{% else %}Players{% endif %}</h2>
        {% if character %}<a href="{{ url_for('dm_players') }}">&larr; Roster</a>{% endif %}
    </div>

    {% with messages = get_flashed_messages() %}
        {% if messages %}
            {% for m in messages %}<div class="flash">{{ m }}</div>{% endfor %}
        {% endif %}
    {% endwith %}

{% if character %}
    <div class="flash stale-notice" id="staleNotice" hidden>
        <span id="staleText"></span>
        <button type="button" class="secondary" onclick="window.location.reload();">Reload</button>
    </div>
    <div class="card dm-char-card{{ ' dead-card' if character.dead else '' }}">
        <h3>
            {% if character.dead %}<span class="dead-badge">&#128128; DEAD &mdash;</span>{% endif %}
            <span style="color: {{ character.color }};">{{ character.name }}</span>
            {% if character.class_name %}<span class="char-class">&mdash; {{ character.class_name }}</span>{% endif %}
        </h3>
        {% if character.features or character.class_traits %}
            <ul class="feature-list">
                {% for t in character.class_traits %}<li class="rule">{{ t }}</li>{% endfor %}
                {% for f in character.features %}<li><b>{{ f.name }}</b> &mdash; {{ f.description }}</li>{% endfor %}
            </ul>
        {% endif %}

        <form method="POST" action="{{ url_for('dm_update_stats') }}" class="stats-edit-form">
            <input type="hidden" name="character_id" value="{{ character.id }}">
            <input type="hidden" name="rev_vitals" value="{{ character.revs.vitals }}">
            <input type="hidden" name="rev_abilities" value="{{ character.revs.abilities }}">
            <div class="sheet-grid">
                {% for key, label in ability_pairs %}
                    <div class="stat-box">
                        <div class="stat-label">{{ label[:4] }}</div>
                        <input type="number" name="{{ key }}" value="{{ character[key] }}"
                               min="__MIN_ABILITY__" max="__MAX_ABILITY__">
                    </div>
                {% endfor %}
            </div>
            <div class="sheet-grid">
                <div class="stat-box"><div class="stat-label">HP</div>
                    <input type="number" name="hp" value="{{ character.hp }}" min="__MIN_HP__" max="__MAX_HP__"></div>
                <div class="stat-box"><div class="stat-label">Max HP</div>
                    <input type="number" name="max_hp" value="{{ character.max_hp }}" min="1" max="__MAX_HP__"></div>
                <div class="stat-box"><div class="stat-label">Omens</div>
                    <input type="number" name="omens" value="{{ character.omens }}" min="0" max="99"></div>
                <div class="stat-box"><div class="stat-label">Silver</div>
                    <input type="number" name="silver" value="{{ character.silver }}" min="0" max="__MAX_SILVER__"></div>
            </div>
            <button type="submit" class="secondary">Save Stats</button>
        </form>

        <div class="inv-section-head"><b>Conditions</b><span>temporary &mdash; base abilities above are never changed</span></div>
        {% if character.conditions %}
            <p class="hint" style="margin:0 0 6px;">With conditions:
                {% for key, label in ability_pairs %}{{ label }} {{ character.effective[key] | signed }}{{ ', ' if not loop.last else '' }}{% endfor %}
            </p>
        {% endif %}
        {% for c in character.conditions %}
            <form method="POST" action="{{ url_for('dm_remove_condition') }}" class="plain-form condition-admin">
                <input type="hidden" name="character_id" value="{{ character.id }}">
                <input type="hidden" name="condition_id" value="{{ c.id }}">
                <span class="condition-pill"><b>{{ c.name }}</b>{% if c.summary %} {{ c.summary }}{% endif %}</span>
                <button type="submit" class="delete-post-btn">Remove</button>
            </form>
        {% endfor %}
        {% if character.conditions | length < max_conditions %}
            <form method="POST" action="{{ url_for('dm_add_condition') }}" class="plain-form condition-admin">
                <input type="hidden" name="character_id" value="{{ character.id }}">
                <input type="text" name="name" placeholder="Condition, e.g. Poisoned" maxlength="{{ max_condition_name }}" required>
                {% for key, label in ability_pairs %}
                    <label>{{ label[:3] }}
                        <input type="number" name="{{ key }}" value="0" min="-{{ max_condition_mod }}" max="{{ max_condition_mod }}" step="1">
                    </label>
                {% endfor %}
                <button type="submit" class="secondary">Apply</button>
            </form>
        {% endif %}

        <form method="POST" action="{{ url_for('dm_update_kit') }}" class="dm-inv-form">
            <input type="hidden" name="character_id" value="{{ character.id }}">
            <input type="hidden" name="rev_kit" value="{{ character.revs.kit }}">
            <div class="dm-inv-grid">
                <div class="inv-slot"><label>Weapon</label>
                    <input type="text" name="weapon" maxlength="{{ max_item_len }}" value="{{ character.weapon }}"></div>
                <div class="inv-slot"><label>Armor</label>
                    <input type="text" name="armor" maxlength="{{ max_item_len }}" value="{{ character.armor }}"></div>
                <div class="inv-slot"><label>Armor tier</label>
                    <input type="number" name="armor_tier" min="0" max="3" value="{{ character.armor_tier }}"></div>
            </div>
            <button type="submit" class="secondary">Save Kit</button>
        </form>

        {% if character.traits %}
            <div class="trait-list">
                {% for key, val in character.traits.items() %}
                    <span class="trait-pill"><span class="trait-key">{{ key }}</span>{{ val }}</span>
                {% endfor %}
            </div>
        {% endif %}

        <p class="hint" style="margin-bottom:2px;">Inventory &mdash; on person {{ character.carried }} / {{ character.capacity }}{% if character.carried > character.capacity * 2 %} (impossible){% elif character.carried > character.capacity %} (overloaded){% endif %}{% if character.containers %}, in containers {{ character.stored }} / {{ character.storage }}{% endif %}</p>
        <form method="POST" action="{{ url_for('dm_update_inventory') }}" class="dm-inv-form">
            <input type="hidden" name="character_id" value="{{ character.id }}">
            <input type="hidden" name="rev_inventory" value="{{ character.revs.inventory }}">
            <div class="inv-section-head"><b>On person</b></div>
            <div class="free-slot">
                <label>Free</label>
                <input type="text" name="free" maxlength="{{ max_item_len }}" value="{{ character.free_item }}"
                       placeholder="Nearly weightless, doesn't count">
            </div>
            <div class="dm-inv-grid">
                {% for i in range(slot_count) %}
                    <div class="inv-slot">
                        <label>{{ i + 1 }}</label>
                        <input type="text" name="slot" maxlength="{{ max_item_len }}" value="{{ character.inventory[i] }}">
                    </div>
                {% endfor %}
            </div>
            {% for c in character.containers %}
                <div class="container-box">
                    <div class="inv-section-head"><b>{{ c.name }}</b>
                        <span>{{ c['items'] | select | list | length }} / {{ c.capacity }}</span></div>
                    <div class="dm-inv-grid">
                        {% for item in c['items'] %}
                            <div class="inv-slot">
                                <label>{{ loop.index }}</label>
                                <input type="text" name="c-{{ c.id }}" maxlength="{{ max_item_len }}" value="{{ item }}">
                            </div>
                        {% endfor %}
                    </div>
                </div>
            {% endfor %}
            <button type="submit" class="secondary">Save Inventory</button>
        </form>

        <div class="inv-section-head"><b>Containers</b><span>items in a removed container are lost</span></div>
        {% for c in character.containers %}
            <form method="POST" action="{{ url_for('dm_update_container') }}" class="plain-form container-admin">
                <input type="hidden" name="character_id" value="{{ character.id }}">
                <input type="hidden" name="container_id" value="{{ c.id }}">
                <input type="text" name="name" value="{{ c.name }}" maxlength="{{ max_container_name }}" required>
                <input type="number" name="capacity" value="{{ c.capacity }}" min="1" max="{{ max_container_slots }}" required title="Slots">
                <button type="submit" class="secondary">Save</button>
                <button type="submit" class="delete-post-btn" formaction="{{ url_for('dm_remove_container') }}" formnovalidate
                        data-confirm="Remove the {{ c.name }} from {{ character.name }}? Everything in it is lost."
                        onclick="return confirm(this.dataset.confirm);">Remove</button>
            </form>
        {% endfor %}
        {% if character.containers | length < max_containers %}
            <form method="POST" action="{{ url_for('dm_add_container') }}" class="plain-form container-admin">
                <input type="hidden" name="character_id" value="{{ character.id }}">
                <select onchange="if (this.value) { const p = this.value.split('|'); this.form.elements['name'].value = p[0]; this.form.elements['capacity'].value = p[1]; }">
                    <option value="">Preset&hellip;</option>
                    {% for name, cap in container_presets %}
                        <option value="{{ name }}|{{ cap }}">{{ name }} ({{ cap }})</option>
                    {% endfor %}
                </select>
                <input type="text" name="name" placeholder="Container name" maxlength="{{ max_container_name }}" required>
                <input type="number" name="capacity" placeholder="Slots" min="1" max="{{ max_container_slots }}" required title="Slots">
                <button type="submit" class="secondary">Add Container</button>
            </form>
        {% endif %}

        <p class="hint" style="margin-top:10px;">Created {{ character.created }}</p>

        <div class="dm-actions">
            <form method="POST" action="{{ url_for('dm_toggle_dead') }}" class="plain-form"
                  {% if not character.dead %}onsubmit="return confirm('Mark {{ character.name }} as dead?');"{% endif %}>
                <input type="hidden" name="character_id" value="{{ character.id }}">
                {% if character.dead %}
                    <button type="submit" class="revive-btn">Revive</button>
                {% else %}
                    <button type="submit" class="delete-post-btn">Mark Dead</button>
                {% endif %}
            </form>

            <form method="POST" action="{{ url_for('dm_delete_character') }}" class="plain-form"
                  onsubmit="return confirm('Permanently delete {{ character.name }}? Anyone logged in as them is sent back to character creation. This cannot be undone.');">
                <input type="hidden" name="character_id" value="{{ character.id }}">
                <button type="submit" class="delete-post-btn">Delete</button>
            </form>
        </div>

        <div class="dm-attach">
            <span class="attach-badge attached">Player login</span>
            <div class="login-row">
                <span class="login-key">User</span>
                <input type="text" readonly value="{{ character.username }}" class="login-field" onclick="this.select();">
                <span class="login-key">Pass</span>
                <input type="text" readonly value="{{ character.password }}" class="login-field" onclick="this.select();">
            </div>
            <div class="login-row">
                <button type="button" class="secondary"
                        data-login="Username: {{ character.username }}&#10;Password: {{ character.password }}"
                        onclick="copyText(this.dataset.login, this)">Copy Login</button>
                <form method="POST" action="{{ url_for('dm_reset_login') }}" class="plain-form" style="display:inline;"
                      onsubmit="return confirm('Give {{ character.name }} a new password? Anyone logged in with the old one is signed out.');">
                    <input type="hidden" name="character_id" value="{{ character.id }}">
                    <button type="submit" class="secondary">Reset Password</button>
                </form>
            </div>
        </div>
    </div>
{% else %}
    <div id="rosterLiving"></div>
    <div class="empty" id="rosterEmpty" hidden>No characters created yet.</div>
    <details class="graveyard" id="graveyard" hidden>
        <summary>Graveyard (<span id="deadCount">0</span>)</summary>
        <div id="rosterDead"></div>
    </details>
{% endif %}

    <script>
        // --- copy player login ---
        function copyText(text, btn) {
            const finish = (ok) => {
                const original = btn.textContent;
                btn.textContent = ok ? 'Copied!' : 'Copy failed';
                setTimeout(() => { btn.textContent = original; }, 1500);
            };
            if (navigator.clipboard && navigator.clipboard.writeText) {
                navigator.clipboard.writeText(text).then(() => finish(true), () => finish(false));
            } else {
                const ta = document.createElement('textarea');
                ta.value = text;
                document.body.appendChild(ta);
                ta.select();
                try { document.execCommand('copy'); finish(true); } catch (e) { finish(false); }
                ta.remove();
            }
        }

        const STATE_URL = '{{ url_for("dm_players_state") }}';
    {% if character %}
        // --- editor: warn if the player changes this character underneath us ---
        const CHAR_ID = {{ character.id | tojson }};
        const PAGE_REVS = {{ character.revs | tojson }};
        const SECTION_NAMES = { vitals: 'HP, omens or silver', abilities: 'abilities',
                                kit: 'kit', inventory: 'inventory', conditions: 'conditions' };

        async function checkStale() {
            try {
                const resp = await fetch(STATE_URL);
                if (!resp.ok) return;
                const data = await resp.json();
                const row = data.characters.find(c => c.id === CHAR_ID);
                let text = '';
                if (!row) {
                    text = 'This character has been deleted.';
                } else {
                    const changed = Object.keys(SECTION_NAMES).filter(k => (row.revs[k] || 0) !== (PAGE_REVS[k] || 0));
                    if (changed.length) {
                        text = row.name + ' changed their ' + changed.map(k => SECTION_NAMES[k]).join(' and ') +
                               '. Reload before saving those sections, or the save will be refused.';
                    }
                }
                const notice = document.getElementById('staleNotice');
                document.getElementById('staleText').textContent = text;
                notice.hidden = !text;
            } catch (e) { /* try again next tick */ }
        }
        setInterval(checkStale, 4000);
    {% else %}
        // --- roster ---
        const QUICK_URL = '{{ url_for("dm_quick_adjust") }}';
        const EDIT_URL = '{{ url_for("dm_player", character_id="__ID__") }}';
        let roster = {{ roster | tojson }};

        function el(tag, cls, text) {
            const e = document.createElement(tag);
            if (cls) e.className = cls;
            if (text !== undefined) e.textContent = text;
            return e;
        }

        function openEditor(id) { window.location.href = EDIT_URL.replace('__ID__', encodeURIComponent(id)); }

        function nudge(row, field, label, valueText) {
            const wrap = el('div', 'nudge');
            wrap.appendChild(el('span', 'k', label));
            const minus = el('button', 'secondary', '\u2212');
            minus.type = 'button';
            minus.title = label + ' \u22121';
            minus.addEventListener('click', () => quick(row, field, -1));
            const plus = el('button', 'secondary', '+');
            plus.type = 'button';
            plus.title = label + ' +1';
            plus.addEventListener('click', () => quick(row, field, 1));
            wrap.appendChild(minus);
            wrap.appendChild(el('span', 'v', valueText));
            wrap.appendChild(plus);
            return wrap;
        }

        function nameCell(row) {
            const cell = el('div', 'roster-name');
            const name = el('b', '', row.name);
            if (row.color) name.style.color = row.color;
            cell.appendChild(name);
            cell.appendChild(el('span', 'sub', row.class_name || 'Classless'));
            if (!row.dead) {
                (row.conditions || []).forEach(name => cell.appendChild(el('span', 'roster-badge cond', name)));
                if (row.hp === 0) cell.appendChild(el('span', 'roster-badge', 'Broken'));
                if (row.carried > row.capacity * 2) cell.appendChild(el('span', 'roster-badge', 'Impossible load'));
                else if (row.carried > row.capacity) cell.appendChild(el('span', 'roster-badge warn', 'Overloaded'));
            }
            cell.title = 'Open ' + row.name;
            cell.addEventListener('click', () => openEditor(row.id));
            return cell;
        }

        function buildRow(row) {
            const div = el('div', 'roster-row' + (row.dead ? ' dead' : ''));
            div.appendChild(nameCell(row));
            if (row.dead) {
                const open = el('button', 'secondary roster-open', 'Open');
                open.type = 'button';
                open.addEventListener('click', () => openEditor(row.id));
                div.appendChild(open);
                return div;
            }
            div.appendChild(nudge(row, 'hp', 'HP', row.hp + ' / ' + row.max_hp));
            div.appendChild(nudge(row, 'omens', 'Omens', String(row.omens)));
            const load = el('div', 'roster-load');
            load.appendChild(document.createTextNode('On person '));
            load.appendChild(el('b', '', row.carried + ' / ' + row.capacity));
            if (row.storage) {
                load.appendChild(document.createElement('br'));
                load.appendChild(document.createTextNode('Containers '));
                load.appendChild(el('b', '', row.stored + ' / ' + row.storage));
            }
            div.appendChild(load);
            return div;
        }

        function render() {
            const living = document.getElementById('rosterLiving');
            const dead = document.getElementById('rosterDead');
            living.replaceChildren(...roster.filter(r => !r.dead).map(buildRow));
            const deadRows = roster.filter(r => r.dead);
            dead.replaceChildren(...deadRows.map(buildRow));
            document.getElementById('deadCount').textContent = deadRows.length;
            document.getElementById('graveyard').hidden = deadRows.length === 0;
            document.getElementById('rosterEmpty').hidden = roster.length !== 0;
        }

        let busy = false;
        async function quick(row, field, delta) {
            if (busy) return;
            if (field === 'hp' && row.hp + delta < {{ min_hp }}) return;
            if (field === 'hp' && row.hp + delta < 0 &&
                !confirm('Negative HP kills ' + row.name + '. Continue?')) return;
            busy = true;
            try {
                const resp = await fetch(QUICK_URL, {
                    method: 'POST',
                    headers: { 'Content-Type': 'application/json' },
                    body: JSON.stringify({ character_id: row.id, field: field, delta: delta })
                });
                const data = await resp.json().catch(() => ({}));
                if (resp.ok && data.row) {
                    roster = roster.map(r => r.id === data.row.id ? data.row : r);
                    render();
                } else {
                    alert(data.error || 'Could not save.');
                }
            } catch (e) {
                alert('Could not save.');
            } finally {
                busy = false;
            }
        }

        async function refresh() {
            if (busy) return;
            try {
                const resp = await fetch(STATE_URL);
                if (!resp.ok) return;
                const data = await resp.json();
                if (JSON.stringify(data.characters) !== JSON.stringify(roster)) {
                    roster = data.characters;
                    render();
                }
            } catch (e) { /* try again next tick */ }
        }

        render();
        setInterval(refresh, 4000);
    {% endif %}
    </script>
</body>
</html>
"""
DM_PLAYERS_TEMPLATE = (
    DM_PLAYERS_TEMPLATE
    .replace('__MIN_ABILITY__', str(MIN_ABILITY))
    .replace('__MAX_ABILITY__', str(MAX_ABILITY))
    .replace('__MIN_HP__', str(MIN_HP))
    .replace('__MAX_HP__', str(MAX_HP))
    .replace('__MAX_SILVER__', str(MAX_SILVER))
)


# ---------------------------------------------------------------------------
# TEMPLATE: rules pop-out (and the "file is missing" version of it)
# ---------------------------------------------------------------------------
DOC_CSS = """
<style>
    :root {
        --ink:#08070a; --bone:#ded7c4; --acid:#f2e50b; --rot:#ff2d6f;
        --blood:#8f1109; --ash:#6b665e; --edge:#2a2730;
        --display:"UnifrakturCook","Cloister Black",Impact,serif;
        --body:"Barlow Condensed","Arial Narrow",Haettenschweiler,sans-serif;
    }
    * { box-sizing: border-box; }
    html { background:#17161a; }
    body {
        font-family: var(--body); font-size: 18px; line-height: 1.4;
        background: #17161a; color: var(--bone);
        margin: 0 auto; padding: 28px 26px 80px; max-width: 860px;
    }
    .doc-head { border-bottom: 6px solid var(--acid); margin-bottom: 26px; padding-bottom: 12px; }
    .doc-head h1 {
        font-family: var(--display); font-weight: 700; font-size: 2.8em;
        line-height: .9; margin: 0; color: var(--acid); text-shadow: 3px 4px 0 var(--blood);
    }
    .doc-head p { margin: 8px 0 0; color: var(--ash); letter-spacing: .16em; text-transform: uppercase; font-size: .8em; }
    h1 { font-family: var(--display); font-weight: 700; font-size: 2.2em; line-height: .95;
         color: var(--acid); margin: 40px 0 4px; border-bottom: 4px solid var(--rot); padding-bottom: 6px; }
    h2, h3 { color: var(--bone); font-weight: 900; text-transform: uppercase; letter-spacing: .08em;
             margin: 26px 0 6px; font-size: 1.15em; }
    h4, h5, h6 { color: var(--rot); font-weight: 900; text-transform: uppercase; letter-spacing: .1em;
                 margin: 20px 0 4px; font-size: 1em; }
    p { margin: 0 0 .7em; }
    strong { color: var(--acid); font-weight: 900; }
    em { color: #efe9d8; }
    u { text-decoration: none; }
    hr { border: none; border-top: 2px solid var(--edge); margin: 26px 0; }
    ul, ol { margin: .4em 0 1em; padding-left: 24px; }
    ol { padding-left: 28px; }
    li { margin-bottom: .35em; }
    li::marker { color: var(--acid); font-weight: 900; }
    /* Nested lists (a d4 sub-table inside one entry) get their own accent so
       the two levels don't read as one run of results. */
    li ul, li ol { margin: .4em 0 .2em; border-left: 2px solid var(--edge); padding-left: 22px; }
    li li::marker { color: var(--rot); }
    blockquote {
        margin: 16px 0; padding: 10px 0 10px 16px;
        border-left: 6px solid var(--rot);
        font-family: var(--display); font-size: 1.35em; line-height: 1.15;
        color: var(--acid);
    }
    table { border-collapse: collapse; width: 100%; margin: 10px 0 20px; font-size: .95em; }
    th { background: var(--acid); color: var(--ink); text-align: left; font-weight: 900;
         text-transform: uppercase; letter-spacing: .06em; padding: 6px 9px; }
    td { border-top: 1px solid var(--edge); padding: 6px 9px; vertical-align: top; }
    tr:nth-child(even) td { background: rgba(255,255,255,.025); }
    td:first-child { color: var(--acid); font-weight: 900; white-space: nowrap; }
    .doc-note { border: 2px dashed var(--ash); padding: 14px 16px; margin-bottom: 26px; color: var(--ash); }
    .doc-note code { color: var(--bone); background: #0b0a0d; padding: 1px 5px; }
    .colophon { margin-top: 50px; border-top: 4px solid var(--ash); padding-top: 12px;
                color: var(--ash); font-size: .8em; letter-spacing: .14em; text-transform: uppercase; }
</style>
"""

DOC_HEAD = """
<!doctype html>
<html lang="en">
<head>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <title>{{ title }}</title>
    <link rel="preconnect" href="https://fonts.googleapis.com">
    <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
    <link href="https://fonts.googleapis.com/css2?family=UnifrakturCook:wght@700&family=Barlow+Condensed:ital,wght@0,400;0,600;0,900;1,400;1,900&display=swap" rel="stylesheet">
""" + DOC_CSS + """
</head>
<body>
    <div class="doc-head">
        <h1>{{ heading }}</h1>
        {% if subtitle %}<p>{{ subtitle }}</p>{% endif %}
    </div>
"""

DOC_TEMPLATE = DOC_HEAD + """
    {{ body | safe }}
    <div class="colophon">{{ colophon }}</div>
</body>
</html>
"""

DOC_MISSING_TEMPLATE = DOC_HEAD + """
    <div class="doc-note">
        <p><strong>Not added yet.</strong></p>
        <p>{{ message }}</p>
        {% if filenames %}
            <p>Expected filenames:</p>
            <ul>{% for f in filenames %}<li><code>{{ f }}</code></li>{% endfor %}</ul>
        {% endif %}
        <p>Drop the file in, then reload this window.</p>
    </div>
</body>
</html>
"""


# ---------------------------------------------------------------------------
# Precompile templates once at startup.
#
# render_template_string() re-parses the entire template source (all the CSS
# and JS included) on *every single request*, which is real, measurable CPU
# time on a Raspberry Pi. Compiling each template once here and calling
# .render() on the cached Template object avoids that re-parsing while still
# giving templates full access to Flask's request/session/url_for/flash
# machinery (via update_template_context, same as render_template_string
# uses internally).
# ---------------------------------------------------------------------------
from flask import current_app

NOTES_TEMPLATE = """
<!doctype html>
<html lang="en">
<head>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <title>Notes &mdash; {{ owner_name }}</title>
""" + FAVICON + SHARED_CSS + """
<style>
    body { max-width: 640px; }
    .notes-card textarea { min-height: 360px; resize: vertical; font-size: 1.05em; line-height: 1.4; }
    .notes-foot { display: flex; justify-content: space-between; align-items: center; gap: 10px; margin-top: 6px; }
    .notes-foot .char-count.over { color: var(--rot); font-weight: 900; }
    .notes-foot button { margin: 0; }
</style>
</head>
<body>
    <div class="card notes-card">
        <h2>Notes</h2>
        <div class="h-under"></div>
        <p class="hint">{{ owner_name }} &mdash; private. Only you can see these notes.</p>
        {% if read_only %}
            <p class="hint">This character has died. Their notes can be read but no longer changed.</p>
        {% endif %}
        <textarea id="notes" maxlength="{{ max_notes }}" placeholder="Names, debts, grudges, omens..."
                  {{ 'readonly' if read_only else '' }}>{{ notes }}</textarea>
        <div class="notes-foot">
            <span class="char-count" id="notesCount"></span>
            <span class="inv-status" id="notesStatus"></span>
            {% if not read_only %}<button type="button" id="notesSave" class="secondary">Save</button>{% endif %}
        </div>
    </div>

    <script>
        const MAX = {{ max_notes }};
        const box = document.getElementById('notes');
        const count = document.getElementById('notesCount');
        const status = document.getElementById('notesStatus');
        const saveUrl = '{{ url_for("save_notes", who=who) }}';
        let saved = box.value;
        let timer = null;

        function updateCount() {
            count.textContent = box.value.length + ' / ' + MAX;
            count.classList.toggle('over', box.value.length >= MAX);
        }

        async function save() {
            clearTimeout(timer);
            if (box.value === saved) { status.textContent = 'Saved.'; return; }
            const text = box.value;
            status.textContent = 'Saving...';
            try {
                const resp = await fetch(saveUrl, {
                    method: 'POST',
                    headers: { 'Content-Type': 'application/json' },
                    body: JSON.stringify({ notes: text })
                });
                const data = await resp.json().catch(() => ({}));
                if (resp.ok) {
                    saved = text;
                    status.textContent = 'Saved.';
                } else {
                    status.textContent = data.error || 'Could not save.';
                }
            } catch (e) {
                status.textContent = 'Could not save.';
            }
        }

        updateCount();
        {% if not read_only %}
        box.addEventListener('input', function () {
            updateCount();
            status.textContent = 'Unsaved...';
            clearTimeout(timer);
            timer = setTimeout(save, 800);
        });
        document.getElementById('notesSave').addEventListener('click', save);
        // Flush anything unsaved when the window is closed or hidden.
        document.addEventListener('visibilitychange', function () {
            if (document.visibilityState === 'hidden' && box.value !== saved && navigator.sendBeacon) {
                navigator.sendBeacon(saveUrl, new Blob([JSON.stringify({ notes: box.value })],
                                                       { type: 'application/json' }));
                saved = box.value;
            }
        });
        {% endif %}
    </script>
</body>
</html>
"""

_NOTES_TPL = app.jinja_env.from_string(NOTES_TEMPLATE)
_CREATE_TPL = app.jinja_env.from_string(CREATE_TEMPLATE)
_BOARD_TPL = app.jinja_env.from_string(BOARD_TEMPLATE)
_DEATH_TPL = app.jinja_env.from_string(DEATH_TEMPLATE)
_DM_LOGIN_TPL = app.jinja_env.from_string(DM_LOGIN_TEMPLATE)
_DM_DASHBOARD_TPL = app.jinja_env.from_string(DM_DASHBOARD_TEMPLATE)
_DM_PLAYERS_TPL = app.jinja_env.from_string(DM_PLAYERS_TEMPLATE)
_DOC_TPL = app.jinja_env.from_string(DOC_TEMPLATE)
_DOC_MISSING_TPL = app.jinja_env.from_string(DOC_MISSING_TEMPLATE)

ABILITY_PAIRS = list(zip(ABILITY_KEYS, ABILITIES))


def render_cached(template, **context):
    current_app.update_template_context(context)
    return template.render(context)


# ---------------------------------------------------------------------------
# Routes: main board / character creation
# ---------------------------------------------------------------------------
@app.errorhandler(413)
def request_too_large(e):
    flash('That request was too large.')
    return redirect(url_for('index'))


def posts_visible_to(character):
    """Player-facing visibility rule, shared by index() and /api/feed: a
    private whisper only ever shows to the character it targets, and a
    player's whisper to the DM only shows to the character who sent it."""
    return [
        post for post in posts
        if not post.get('is_private')
        or post.get('target_character_id') == character['id']
        or (post.get('to_dm') and post.get('author_character_id') == character['id'])
    ]


def serialize_post(post, viewer=None):
    """JSON shape consumed by the /api/feed poller. message_html is
    pre-rendered server-side via format_message() (safe to insert as-is).
    Every other user-influenced field (username, roll labels/descriptions) is
    HTML-escaped here, since Jinja's autoescaping — which normally protects
    these on the initial page render — doesn't apply to JSON responses the
    client inserts via innerHTML."""
    return {
        'id': post.get('id'),
        'seq': post.get('seq', 0),
        'is_dm': bool(post.get('is_dm')),
        'is_private': bool(post.get('is_private')),
        'to_dm': bool(post.get('to_dm')),
        'target_character_name': escape(post.get('target_character_name', '')),
        'username': escape(post.get('username', '')),
        'char_class': escape(post.get('char_class', '')),
        'color': post.get('color', PLAYER_COLORS[0]),
        'message_html': format_message(post.get('message', '')),
        'edited': bool(post.get('edited')),
        **dict(zip(('edit_seconds_left', 'can_delete'), own_post_permissions(post, viewer))),
        # Unformatted text for the author's edit box. Only sent to the author
        # while they can still edit, and only ever assigned as plain text.
        **({'message_raw': post.get('message', '')} if own_post_permissions(post, viewer)[0] > 0 else {}),
        'rolls': [
            {
                'label': escape(r.get('label', '')),
                'description': escape(r.get('description', '')),
                'total': r.get('total', 0)
            }
            for r in post.get('rolls', [])
        ],
        'timestamp': post.get('timestamp', ''),
    }


def class_info_for_wizard():
    """The blurb and bullets shown beside each class in the creation wizard.
    Keyed by class name, with '' for the classless build."""
    info = {'': {'blurb': '', 'bullets': CLASSLESS_BULLETS, 'ability_note': ''}}
    for name, cls in CLASSES.items():
        mods = cls['ability_mods']
        note = ('This class sets its own ability modifiers: '
                # Typographic minus, to match the bullets rather than the
                # ASCII hyphen signed() uses for the numeric stat boxes.
                + ', '.join(f'{k.title()} {signed(v).replace("-", chr(0x2212))}'
                            for k, v in mods.items())
                + '.') if mods else 'This class applies no ability modifiers.'
        info[name] = {
            'blurb': cls['blurb'],
            'bullets': cls['bullets'],
            'ability_note': note,
        }
    return info


@app.route('/')
def index():
    character = get_character()
    if not character:
        return render_cached(_CREATE_TPL,
                             ability_choices=ABILITY_PAIRS,
                             class_names=list(CLASSES.keys()),
                             class_info=class_info_for_wizard())

    if character.get('dead'):
        return render_cached(_DEATH_TPL, character=character)

    visible_posts = posts_visible_to(character)

    return render_cached(
        _BOARD_TPL,
        notes_for='player',
        mention_self=character['name'],
        character=character,
        ability_pairs=ABILITY_PAIRS,
        slot_count=INVENTORY_SLOTS,
        capacity=carrying_capacity(effective_ability(character, 'strength')),
        effective=effective_abilities(character),
        conditions=public_conditions(character),
        max_item_len=MAX_ITEM_LENGTH,
        posts=[{**p, **dict(zip(('edit_seconds_left', 'can_delete'), own_post_permissions(p, character)))}
               for p in reversed(visible_posts)],
        latest_change=_feed_change,
        max_len=MAX_MESSAGE_LENGTH,
        dice_types=list(DICE_TYPES.keys()),
        max_dice_per_type=MAX_DICE_PER_TYPE,
        max_rolls_per_post=MAX_ROLLS_PER_POST,
        max_roll_label_len=MAX_ROLL_LABEL_LENGTH,
        latest_seq=max((p.get('seq', 0) for p in visible_posts), default=-1)
    )


def own_post_or_error(post_id):
    """(character, post, seconds_left, may_delete), or a JSON error response."""
    character = get_character()
    if not character:
        return None, (jsonify({'error': 'Not logged in.'}), 403)
    post = next((p for p in posts if p.get('id') == post_id), None)
    if not post or post.get('author_character_id') != character['id'] or post.get('is_dm'):
        return None, (jsonify({'error': 'That post is not yours to change.'}), 403)
    left, may_delete = own_post_permissions(post, character)
    if left <= 0:
        return None, (jsonify({'error': 'Posts can only be changed for '
                                        f'{POST_EDIT_WINDOW_SECONDS // 60} minutes after sending.'}), 403)
    return (character, post, left, may_delete), None


@app.route('/post/<post_id>/edit', methods=['POST'])
def edit_own_post(post_id):
    """JSON only, like the other autosave endpoints. Only the text changes —
    rolls, whisper target and timestamp stay as they were."""
    found, error = own_post_or_error(post_id)
    if error:
        return error
    character, post, _, _ = found

    data = request.get_json(silent=True)
    if not isinstance(data, dict) or not isinstance(data.get('message'), str):
        return jsonify({'error': 'Invalid request.'}), 400
    message = data['message'].strip()
    if not message:
        return jsonify({'error': 'Message cannot be empty. Delete the post instead.'}), 400
    if len(message) > MAX_MESSAGE_LENGTH:
        return jsonify({'error': f'Message cannot exceed {MAX_MESSAGE_LENGTH} characters.'}), 400

    if message != post['message']:
        original = post['message']
        post['message'] = message
        post['edited'] = True
        post['change'] = next_feed_change()
        save_posts()
        log_activity(character['name'], 'EDITED_MESSAGE',
                     f'post_id={post_id}, from="{original}" to="{message}"')

    return jsonify({'ok': True, 'post': serialize_post(post, character)})


@app.route('/post/<post_id>/delete', methods=['POST'])
def delete_own_post(post_id):
    global posts
    found, error = own_post_or_error(post_id)
    if error:
        return error
    character, post, _, may_delete = found
    if not may_delete:
        return jsonify({'error': 'Posts with dice rolls can\'t be deleted. You can still edit the text.'}), 403
    # Require the JSON content type, so a cross-site form can't trigger this.
    if not request.is_json:
        return jsonify({'error': 'Invalid request.'}), 400

    posts = [p for p in posts if p.get('id') != post_id]
    save_posts()
    record_post_deletion(post_id)
    log_activity(character['name'], 'DELETED_OWN_MESSAGE', f'post_id={post_id}, message="{post["message"]}"')
    return jsonify({'ok': True})


@app.route('/api/mentions')
def api_mentions():
    """Living characters for the @mention picker. Names are already public
    to anyone at the table (they're on every post), so this reveals nothing
    new — but it's still limited to logged-in players and the DM."""
    if not session.get('is_dm') and not get_character():
        return jsonify({'error': 'Not logged in.'}), 403
    living = sorted((c for c in characters.values() if not c.get('dead') and c.get('name')),
                    key=lambda c: c['name'].lower())
    return jsonify({'characters': [{'name': c['name'], 'color': c.get('color', '')} for c in living]})


@app.route('/api/feed')
def api_feed():
    """Polled by the board and DM dashboard to pull in new posts (and scene
    changes) without a full page reload. Returns only posts with seq greater
    than after_seq, oldest-of-the-batch first, so the client can prepend
    them in order and end up with newest-on-top."""

    try:
        after_seq = int(request.args.get('after_seq', -1))
    except (TypeError, ValueError):
        after_seq = -1

    try:
        after_change = int(request.args.get('after_change', -1))
    except (TypeError, ValueError):
        after_change = -1

    viewer = None
    if session.get('is_dm'):
        candidates = posts
    else:
        character = get_character()
        if not character:
            return jsonify({'error': 'No character found.'}), 404
        candidates = posts_visible_to(character)
        viewer = character

    new_posts = sorted(
        (p for p in candidates if p.get('seq', -1) > after_seq),
        key=lambda p: p.get('seq', 0)
    )
    latest_seq = max((p.get('seq', 0) for p in candidates), default=after_seq)

    # Edits to posts this client already shows, and posts deleted since.
    # A client that hasn't got a cursor yet (-1) gets none: its page was
    # rendered with everything current.
    updates, deleted = [], []
    if after_change >= 0:
        updates = [serialize_post(p, viewer) for p in candidates
                   if p.get('change', 0) > after_change and p.get('seq', -1) <= after_seq]
        deleted = [post_id for change, post_id in _recent_deletions if change > after_change]

    payload = {
        'posts': [serialize_post(p, viewer) for p in new_posts],
        'updates': updates,
        'deleted': deleted,
        'latest_seq': latest_seq,
        'latest_change': _feed_change,
        'scene_name': scene_name
    }
    # Lets an open board pick up changes the DM made to this character.
    if request.args.get('sheet'):
        character = get_character()
        if character:
            payload['sheet'] = sheet_state(character)
    return jsonify(payload)


# ---------------------------------------------------------------------------
# Routes: pop-out documents (rules + adventures)
# ---------------------------------------------------------------------------
# ---------------------------------------------------------------------------
# Routes: private notes
# ---------------------------------------------------------------------------
# `who` says whose notes the window is for, because one browser can be logged
# in as a player and as the DM at the same time. The session decides whether
# that's allowed — the URL alone never grants access.
def notes_owner(who):
    """(display name, character or None) if this session may use `who`'s
    notes, else None."""
    if who == 'dm':
        return ('Dungeon Master', None) if session.get('is_dm') else None
    if who == 'player':
        character = get_character()
        return (character['name'], character) if character else None
    return None


@app.route('/notes/<who>')
def notes(who):
    owner = notes_owner(who)
    if not owner:
        abort(403)
    name, character = owner
    return render_cached(
        _NOTES_TPL,
        who=who,
        owner_name=name,
        notes=dm_notes if character is None else character.get('notes', ''),
        read_only=bool(character and character.get('dead')),
        max_notes=MAX_NOTES_LENGTH,
    )


@app.route('/notes/<who>/save', methods=['POST'])
def save_notes(who):
    global dm_notes
    owner = notes_owner(who)
    if not owner:
        return jsonify({'error': 'Not logged in.'}), 403
    name, character = owner
    if character and character.get('dead'):
        return jsonify({'error': 'This character has died.'}), 403

    # JSON only: a plain cross-site HTML form can't send this content type.
    data = request.get_json(silent=True)
    if not isinstance(data, dict) or not isinstance(data.get('notes'), str):
        return jsonify({'error': 'Invalid notes payload.'}), 400

    text = clean_notes(data['notes'])
    if len(text) > MAX_NOTES_LENGTH:
        return jsonify({'error': f'Notes cannot exceed {MAX_NOTES_LENGTH} characters.'}), 400

    if character is None:
        changed = text != dm_notes
        dm_notes = text
        if changed:
            save_dm_notes(text)
    else:
        changed = text != character.get('notes', '')
        character['notes'] = text
        if changed:
            save_characters()

    if changed:
        # Contents stay out of the log: notes are private, the log isn't.
        log_activity('DM' if character is None else name, 'NOTES_UPDATED', f'{len(text)} chars')
    return jsonify({'ok': True})


@app.route('/rules')
def rules():
    body = get_rules_html()
    if body is None:
        return render_cached(
            _DOC_MISSING_TPL,
            title='Rules',
            heading='Rules',
            subtitle='MÖRK BORG',
            message='The rules file needs to sit in the same folder as app.py.',
            filenames=RULES_FILENAMES,
        )
    return render_cached(
        _DOC_TPL,
        title=RULES_TITLE,
        heading='Bare Bones Edition',
        subtitle='MÖRK BORG',
        body=body,
        colophon='MÖRK BORG is copyright Ockult Örtmästare Games and Stockholm Kartell. '
                 'Rules text reproduced here for personal table use.',
    )


@app.route('/adventure/<slug>')
def adventure(slug):
    entry = find_adventure(slug)
    if not entry:
        abort(404)

    if not entry['available']:
        known = next((k for k in KNOWN_ADVENTURES if k['slug'] == slug), None)
        return render_cached(
            _DOC_MISSING_TPL,
            title=entry['title'],
            heading=entry['title'],
            subtitle='Adventure',
            message='Drop the adventure file into the "adventures" folder next to app.py.',
            filenames=known['filenames'] if known else [],
        )

    text = read_text_file(entry['path'])
    if text is None:
        abort(404)

    ext = os.path.splitext(entry['path'])[1].lower()
    if ext in ('.html', '.htm'):
        # Already a complete, styled document — serve it as-is, minus any
        # <script> blocks (see strip_scripts).
        return Response(strip_scripts(text), mimetype='text/html')

    return render_cached(
        _DOC_TPL,
        title=entry['title'],
        heading=entry['title'],
        subtitle='Adventure',
        body=md_to_html(text),
        colophon='An adventure for MÖRK BORG.',
    )


# ---------------------------------------------------------------------------
# Routes: character creation
#
# Every roll is made server-side and stashed in the session draft, so the
# finished character is assembled entirely from values this app generated —
# there are no client-submitted stats to second-guess.
# ---------------------------------------------------------------------------
@app.route('/character/retire', methods=['POST'])
def retire_character():
    """Called from the death screen. Signs this browser out of a dead character
    so index() shows the creation wizard again. The dead character's
    record is left untouched in `characters` so the DM still has it on file."""
    character = get_character()
    if character and character.get('dead'):
        log_out_player()
        log_activity(character['name'], 'CHARACTER_RETIRED', f"id={character['id']}")
    return redirect(url_for('index'))


@app.route('/create/roll-name', methods=['POST'])
def roll_name():
    # d6 picks the block of eight, d8 picks within it
    index = (roll_dn(6) - 1) * 8 + (roll_dn(8) - 1)
    return jsonify({'name': NAMES[index]})


@app.route('/create/roll-abilities', methods=['POST'])
def roll_abilities():
    data = request.get_json(silent=True) or {}
    class_name = data.get('class_name') or ''
    if class_name and class_name not in CLASSES:
        return jsonify({'error': 'Unknown class.'}), 400
    cls = CLASSES.get(class_name)

    abilities = {}
    detail = {}

    if cls:
        # A class fixes its own modifiers, applied to the 3d6 sum before the
        # score table is read, so there's no 4d6 pick to make.
        mods = cls['ability_mods']
        for key in ABILITY_KEYS:
            dice = roll_xdy(3, 6)
            mod = mods.get(key, 0)
            total = sum(dice) + mod
            suffix = f' {signed(mod)}' if mod else ''
            detail[key] = f'3d6 {dice}{suffix} = {total}'
            abilities[key] = ability_from_roll(total)
        hp_die = cls['hp_die']
        omen_die = cls['omen_die']
        silver_dice = cls['silver_dice']
    else:
        # Playing without classes, exactly two abilities use 4d6-drop-lowest.
        boosted = data.get('boosted')
        if not isinstance(boosted, list):
            boosted = []
        boosted = [b for b in boosted if b in ABILITY_KEYS]
        boosted = list(dict.fromkeys(boosted))  # de-dupe, keep order
        if len(boosted) != 2:
            return jsonify({'error': 'Choose exactly two abilities to roll 4d6, drop the lowest.'}), 400

        for key in ABILITY_KEYS:
            if key in boosted:
                dice = roll_xdy(4, 6)
                kept = sorted(dice)[1:]
                total = sum(kept)
                detail[key] = f'4d6 {dice} drop {min(dice)}'
            else:
                dice = roll_xdy(3, 6)
                total = sum(dice)
                detail[key] = f'3d6 {dice}'
            abilities[key] = ability_from_roll(total)
        hp_die, omen_die, silver_dice = 8, 2, 2

    hp = max(1, abilities['toughness'] + roll_dn(hp_die))
    omens = roll_dn(omen_die)
    silver = sum(roll_xdy(silver_dice, 6)) * 10

    draft = session.get('draft', {})
    draft['class_name'] = class_name
    draft['abilities'] = abilities
    draft['hp'] = hp
    draft['omens'] = omens
    draft['silver'] = silver
    draft.pop('gear', None)  # Presence or class changed, so rolled gear is stale
    session['draft'] = draft

    return jsonify({
        'abilities': [
            {'key': key, 'label': label, 'display': signed(abilities[key]), 'detail': detail[key]}
            for key, label in ABILITY_PAIRS
        ],
        'hp': hp,
        'hp_die': hp_die,
        'omens': omens,
        'silver': silver,
    })


@app.route('/create/roll-gear', methods=['POST'])
def roll_gear():
    draft = session.get('draft', {})
    if 'abilities' not in draft:
        return jsonify({'error': 'Roll your abilities first — some gear scales with Presence.'}), 400

    presence = draft['abilities']['presence']
    cls = CLASSES.get(draft.get('class_name') or '')

    container = CONTAINERS[roll_dn(6)]
    items = [gear_table_one(roll_dn(12), presence), gear_table_two(roll_dn(12))]

    def is_scroll(item):
        return 'scroll' in item.lower()

    if cls and cls.get('illiterate'):
        # "If you begin with one then reroll, eat it or use it as toilet paper."
        # Each slot is rerolled on its own table until it isn't a scroll; only
        # one entry per table is a scroll, so this settles almost immediately.
        rerolls = [lambda: gear_table_one(roll_dn(12), presence),
                   lambda: gear_table_two(roll_dn(12))]
        for idx, reroll in enumerate(rerolls):
            guard = 0
            while is_scroll(items[idx]) and guard < 50:
                items[idx] = reroll()
                guard += 1

    if cls and cls.get('bonus_scroll'):
        table = random.choice([UNCLEAN_SCROLLS, SACRED_SCROLLS])
        kind = 'Unclean' if table is UNCLEAN_SCROLLS else 'Sacred'
        items.append(f'{kind} scroll: {random.choice(table)}')

    # A class sets its own weapon/armor dice. Without one, a starting scroll
    # still drops the dice to d6/d2 so a caster isn't handed plate.
    if cls:
        weapon_die = cls['weapon_die']
        armor_die = cls['armor_die']
    elif any(is_scroll(i) for i in items):
        weapon_die, armor_die = SCROLL_WEAPON_DIE, SCROLL_ARMOR_DIE
    else:
        weapon_die, armor_die = 10, 4

    weapon_name, weapon_damage = WEAPONS[roll_dn(weapon_die)]
    weapon = f'{weapon_name} ({weapon_damage})'
    # Bows and crossbows come with Presence-scaled ammunition
    if weapon_name == 'Bow':
        items.append(f'Arrows x{presence_count(presence, 10)}')
    elif weapon_name == 'Crossbow':
        items.append(f'Bolts x{presence_count(presence, 10)}')

    tier = roll_dn(armor_die) - 1
    if cls and cls.get('reroll_heavy_armor'):
        while tier == 3:
            tier = roll_dn(armor_die) - 1
    armor_name, reduction, note = ARMOR[tier]
    armor = ' — '.join(part for part in (armor_name, reduction, note) if part)

    food = roll_dn(4)

    origin = ''
    features = []
    if cls:
        origin = cls['origins'][roll_dn(cls.get('origin_die', 6)) - 1]
        # Wretched Royalty takes two entries, and they must be different ones.
        picks = random.sample(range(6), cls['feature_count']) if cls['feature_count'] else []
        for idx in sorted(picks):
            name, desc = cls['features'][idx]
            features.append({'name': name, 'description': desc})
            items.append(name)
        if cls.get('decoctions'):
            items.append('Portable laboratory')
            for name, desc in random.sample(DECOCTIONS, 2):
                features.append({'name': f'Decoction: {name}', 'description': desc})

    draft['gear'] = {
        'container': container,
        'items': items,
        'weapon': weapon,
        'armor': armor,
        'armor_tier': tier,
        'food': food,
        'origin': origin,
        'features': features,
    }
    session['draft'] = draft

    return jsonify({
        'container': container,
        'items': items,
        'weapon': weapon,
        'armor': armor,
        'food': food,
        'origin': origin,
        'origin_label': cls['origin_label'] if cls else '',
        'features': features,
        'feature_label': cls['feature_label'] if cls else '',
    })


@app.route('/create/roll-flavour', methods=['POST'])
def roll_flavour():
    traits = {key: table[roll_dn(20) - 1] for key, table in TRAIT_TABLES.items()}

    draft = session.get('draft', {})
    draft['traits'] = traits
    session['draft'] = draft

    return jsonify({'traits': [{'key': k, 'value': v} for k, v in traits.items()]})


@app.route('/create/finish', methods=['POST'])
def finish_character():
    draft = session.get('draft', {})

    name = clean_text(request.form.get('name', ''), MAX_USERNAME_LENGTH)

    if not name:
        flash('Your character needs a name.')
        return redirect(url_for('index'))

    if name.strip().lower() == 'dm':
        flash('"DM" is reserved and cannot be used as a character name.')
        return redirect(url_for('index'))

    if 'abilities' not in draft:
        flash('Roll your abilities first.')
        return redirect(url_for('index'))

    if 'gear' not in draft:
        flash('Roll your equipment first.')
        return redirect(url_for('index'))

    gear = draft['gear']
    inventory = list(gear['items'])
    inventory.append(f"Food, {gear['food']} days")
    inventory.append('Waterskin')
    inventory = inventory[:INVENTORY_SLOTS]
    starting_container = container_from_text(gear['container'])
    inventory += [''] * (INVENTORY_SLOTS - len(inventory))

    char_id = str(uuid.uuid4())
    character = {
        'id': char_id,
        'name': name,
        'username': generate_username(taken_usernames(characters)),
        'password': generate_password(),
        'login_version': 1,
        'class_name': draft.get('class_name', ''),
        'origin': gear.get('origin', ''),
        'features': gear.get('features', []),
        'class_traits': CLASSES.get(draft.get('class_name') or '', {}).get('traits', []),
        'color': assign_character_color(characters),
        'hp': draft['hp'],
        'max_hp': draft['hp'],
        'omens': draft['omens'],
        'silver': draft['silver'],
        'weapon': gear['weapon'],
        'armor': gear['armor'],
        'armor_tier': gear['armor_tier'],
        'containers': [starting_container] if starting_container else [],
        'free_item': '',
        'notes': '',
        'revs': {section: 0 for section in REV_SECTIONS},
        'conditions': [],
        'food': gear['food'],
        # Flask's session serializer sorts dict keys, so the draft comes back
        # alphabetised. Rebuild in the order the tables are declared.
        'traits': {k: draft['traits'][k] for k in TRAIT_TABLES if k in draft.get('traits', {})},
        'inventory': inventory,
        'dead': False,
        'created': datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
    }
    character.update(draft['abilities'])
    characters[char_id] = character
    save_characters()
    session.pop('draft', None)
    log_in_as(character)
    flash(f"Write this down — your login is username {character['username']}, "
          f"password {character['password']}. It's also at the bottom of your sheet, "
          f"and the DM can look it up if you lose it.")

    abilities = draft['abilities']
    log_activity(name, 'CHARACTER_CREATED',
                 f"class={draft.get('class_name') or 'classless'}, "
                 f"agi={abilities['agility']}, pre={abilities['presence']}, "
                 f"str={abilities['strength']}, tou={abilities['toughness']}, "
                 f"hp={draft['hp']}, omens={draft['omens']}, silver={draft['silver']}, "
                 f"weapon={gear['weapon']}")

    return redirect(url_for('index'))


# ---------------------------------------------------------------------------
# Routes: player-side character updates
# ---------------------------------------------------------------------------
@app.route('/character/inventory', methods=['POST'])
def update_inventory():
    """Payload: {"slots": [...on your person...], "free": "...",
    "containers": {id: [...]}}.
    Containers the browser doesn't know about are left alone, and a container
    the DM removed while the page was open is ignored rather than recreated."""
    character = get_character()
    if not character:
        return jsonify({'error': 'No character found.'}), 404
    if character.get('dead'):
        return jsonify({'error': 'This character has died.'}), 403

    data = request.get_json(silent=True) or {}
    if not rev_matches(character, 'inventory', data.get('rev')):
        return jsonify({'error': 'The DM changed your inventory. Reload to see it — your last edit was not saved.',
                        'stale': True}), 409
    slots = data.get('slots')
    submitted = data.get('containers') or {}
    if not isinstance(slots, list) or not isinstance(submitted, dict):
        return jsonify({'error': 'Invalid inventory payload.'}), 400

    new_person = fit_items(slots, INVENTORY_SLOTS)
    new_free = fit_items([data.get('free', '')], 1)[0]
    new_containers = {
        c['id']: fit_items(submitted[c['id']], c['capacity'])
        for c in character.get('containers', [])
        if isinstance(submitted.get(c['id']), list)
    }

    changes = inventory_changes(character, new_person, new_containers, new_free)
    character['inventory'] = new_person
    character['free_item'] = new_free
    for c in character.get('containers', []):
        if c['id'] in new_containers:
            c['items'] = new_containers[c['id']]
    if changes:
        bump(character, 'inventory')
    save_characters()

    if changes:
        log_activity(character['name'], 'INVENTORY_UPDATED', '; '.join(changes))

    return jsonify({'ok': True, 'rev': character['revs']['inventory']})


@app.route('/character/stats', methods=['POST'])
def update_stats():
    """HP, Omens and Silver all change constantly in play, so players edit
    them directly on their own sheet. Negative HP is death in MÖRK BORG, so
    this is also where a character dies."""
    character = get_character()
    if not character:
        return jsonify({'error': 'No character found.'}), 404
    if character.get('dead'):
        return jsonify({'error': 'This character has died.'}), 403

    data = request.get_json(silent=True) or {}
    if not rev_matches(character, 'vitals', data.get('rev')):
        return jsonify({'error': 'The DM just changed these — your sheet has been updated.',
                        'stale': True, 'sheet': sheet_state(character)}), 409
    bounds = {'hp': (MIN_HP, MAX_HP), 'omens': (0, 99), 'silver': (0, MAX_SILVER)}
    new_values = {}
    for key, (lo, hi) in bounds.items():
        raw = data.get(key)
        if isinstance(raw, bool) or not isinstance(raw, int):
            return jsonify({'error': f'Invalid value for {key}.'}), 400
        if not (lo <= raw <= hi):
            return jsonify({'error': f'{key} must be between {lo} and {hi}.'}), 400
        new_values[key] = raw

    changes = [f'{k} {character.get(k)}->{v}' for k, v in new_values.items() if character.get(k) != v]
    character.update(new_values)

    died = character['hp'] < 0
    if died:
        character['dead'] = True
    if changes:
        bump(character, 'vitals')

    save_characters()

    if changes:
        log_activity(character['name'], 'STATS_UPDATED', ', '.join(changes))
    if died:
        log_activity(character['name'], 'DIED', f"hp={character['hp']}")

    return jsonify({'ok': True, 'dead': died, 'broken': character['hp'] == 0,
                    'rev': character['revs']['vitals']})


# ---------------------------------------------------------------------------
# Routes: dice roller for posts
# ---------------------------------------------------------------------------
@app.route('/roll', methods=['POST'])
def roll_dice():
    data = request.get_json(silent=True) or {}
    dice = data.get('dice', {})

    if not isinstance(dice, dict) or not dice:
        return jsonify({'error': 'No dice specified.'}), 400

    results = {}
    total = 0
    description_parts = []

    for die, qty in dice.items():
        if die not in DICE_TYPES:
            return jsonify({'error': f'Unknown die type: {die}'}), 400
        if isinstance(qty, bool) or not isinstance(qty, int):
            return jsonify({'error': f'Invalid quantity for {die}.'}), 400
        if qty <= 0:
            continue
        if qty > MAX_DICE_PER_TYPE:
            return jsonify({'error': f'Max {MAX_DICE_PER_TYPE} {die} dice per roll.'}), 400

        sides = DICE_TYPES[die]
        rolls = roll_xdy(qty, sides)
        results[die] = rolls
        total += sum(rolls)
        description_parts.append(f'{qty}{die} {rolls}')

    if not results:
        return jsonify({'error': 'No dice specified.'}), 400

    return jsonify({'results': results, 'total': total, 'description': ' + '.join(description_parts)})


# ---------------------------------------------------------------------------
# Routes: message board posting
# ---------------------------------------------------------------------------
@app.route('/post', methods=['POST'])
def new_post():
    character = get_character()
    if not character:
        flash('Create a character before posting.')
        return redirect(url_for('index'))

    if character.get('dead'):
        flash('Your character has died and cannot post.')
        return redirect(url_for('index'))

    message = request.form.get('message', '').strip()
    rolls_raw = request.form.get('rolls', '[]')

    if not message:
        flash('Message cannot be empty.')
        return redirect(url_for('index'))

    if len(message) > MAX_MESSAGE_LENGTH:
        flash(f'Message cannot exceed {MAX_MESSAGE_LENGTH} characters.')
        return redirect(url_for('index'))

    clean_rolls = parse_submitted_rolls(rolls_raw, character)
    to_dm = request.form.get('whisper_dm') == '1'

    posts.append({
        'id': str(uuid.uuid4()),
        'seq': next_post_seq(),
        'username': character['name'],
        'char_class': character.get('class_name', ''),
        'color': character.get('color', PLAYER_COLORS[0]),
        'message': message,
        'timestamp': datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
        'created_at': datetime.now().timestamp(),
        'rolls': clean_rolls,
        'is_dm': False,
        # A whisper to the DM is private: only the DM and its author see it.
        'is_private': to_dm,
        'to_dm': to_dm,
        'author_character_id': character['id'],
        'target_character_id': None,
        'target_character_name': 'DM' if to_dm else ''
    })
    save_posts()

    log_msg = message if len(message) <= 80 else message[:77] + '...'
    roll_summary = f', rolls={len(clean_rolls)}' if clean_rolls else ''
    log_activity(character['name'], 'WHISPERED_TO_DM' if to_dm else 'POSTED_MESSAGE',
                 f'"{log_msg}"{roll_summary}')

    return redirect(url_for('index'))


# ---------------------------------------------------------------------------
# Routes: DM view (password protected)
# ---------------------------------------------------------------------------
@app.route('/dm')
def dm_home():
    if not session.get('is_dm'):
        return render_cached(_DM_LOGIN_TPL)

    # Character management lives in the Players pop-out (dm_players); the
    # dashboard only needs the list for the whisper picker.
    return render_cached(
        _DM_DASHBOARD_TPL,
        notes_for='dm',
        characters=list(characters.values()),
        adventures=list_adventures(),
        posts=list(reversed(posts)),
        max_len=MAX_MESSAGE_LENGTH,
        max_item_len=MAX_ITEM_LENGTH,
        dice_types=list(DICE_TYPES.keys()),
        max_dice_per_type=MAX_DICE_PER_TYPE,
        max_rolls_per_post=MAX_ROLLS_PER_POST,
        max_roll_label_len=MAX_ROLL_LABEL_LENGTH,
        max_roll_modifier=MAX_ROLL_MODIFIER,
        latest_change=_feed_change,
        latest_seq=max((p.get('seq', 0) for p in posts), default=-1)
    )


@app.route('/dm/login', methods=['POST'])
def dm_login():
    password = request.form.get('password', '')
    if secrets.compare_digest(password, DM_PASSWORD):
        session['is_dm'] = True
        log_activity('DM', 'LOGIN_SUCCESS', f'ip={request.remote_addr}')
    else:
        flash('Incorrect DM password.')
        log_activity('DM', 'LOGIN_FAILED', f'ip={request.remote_addr}')
    return redirect(url_for('dm_home'))


@app.route('/dm/logout')
def dm_logout():
    if session.get('is_dm'):
        log_activity('DM', 'LOGOUT')
    session.pop('is_dm', None)
    return redirect(url_for('index'))


@app.route('/dm/post', methods=['POST'])
def dm_post():
    """The DM's single post form. With no whisper_to it's a general post;
    with a character id it's a whisper only that character (and the DM) sees."""
    if not session.get('is_dm'):
        flash('DM login required.')
        return redirect(url_for('dm_home'))

    target_id = request.form.get('whisper_to', '').strip()
    target = None
    if target_id:
        target = characters.get(target_id)
        if not target:
            flash('That character no longer exists — nothing was posted.')
            return redirect(url_for('dm_home'))
        if target.get('dead'):
            flash(f'{target["name"]} is dead — nothing was posted.')
            return redirect(url_for('dm_home'))

    message = request.form.get('message', '').strip()
    rolls_raw = request.form.get('rolls', '[]')
    if not message:
        flash('DM message cannot be empty.')
        return redirect(url_for('dm_home'))
    # No length cap for DM posts (players are still capped at MAX_MESSAGE_LENGTH).
    # The global 64KB request-body limit (MAX_CONTENT_LENGTH) still applies.

    clean_rolls = parse_submitted_rolls(rolls_raw, allow_modifier=True)

    posts.append({
        'id': str(uuid.uuid4()),
        'seq': next_post_seq(),
        'username': 'DM',
        'char_class': '',
        'color': PLAYER_COLORS[0],
        'message': message,
        'timestamp': datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
        'created_at': datetime.now().timestamp(),
        'rolls': clean_rolls,
        'is_dm': True,
        'is_private': bool(target),
        'target_character_id': target['id'] if target else None,
        # Frozen at send time so the whisper's label stays correct on the DM
        # dashboard even if the character is later renamed.
        'target_character_name': target['name'] if target else ''
    })
    save_posts()

    log_msg = message if len(message) <= 80 else message[:77] + '...'
    roll_summary = f', rolls={len(clean_rolls)}' if clean_rolls else ''
    if target:
        log_activity('DM', 'WHISPERED', f'to={target["name"]}; "{log_msg}"{roll_summary}')
    else:
        log_activity('DM', 'POSTED_MESSAGE', f'"{log_msg}"{roll_summary}')

    return redirect(url_for('dm_home'))


@app.route('/dm/backup')
def dm_backup():
    if not session.get('is_dm'):
        flash('DM login required.')
        return redirect(url_for('dm_home'))

    buf = io.BytesIO()
    with zipfile.ZipFile(buf, 'w', zipfile.ZIP_DEFLATED) as zf:
        for path in (DATA_FILE, CHAR_FILE, SCENE_FILE, DM_NOTES_FILE, LOG_FILE):
            if os.path.exists(path):
                zf.write(path, arcname=os.path.basename(path))
    buf.seek(0)

    log_activity('DM', 'DOWNLOADED_BACKUP')

    timestamp = datetime.now().strftime('%Y%m%d-%H%M%S')
    return send_file(
        buf,
        mimetype='application/zip',
        as_attachment=True,
        download_name=f'morkborg-backup-{timestamp}.zip'
    )


@app.route('/dm/set-scene', methods=['POST'])
def dm_set_scene():
    if not session.get('is_dm'):
        flash('DM login required.')
        return redirect(url_for('dm_home'))

    global scene_name
    new_name = clean_text(request.form.get('scene_name', ''), MAX_SCENE_LENGTH)
    new_name = new_name or DEFAULT_SCENE_NAME

    if new_name != scene_name:
        old_name = scene_name
        scene_name = new_name
        save_scene_name(scene_name)
        log_activity('DM', 'SET_SCENE', f'"{old_name}" -> "{new_name}"')

    return redirect(url_for('dm_home'))


@app.route('/dm/delete-post', methods=['POST'])
def dm_delete_post():
    if not session.get('is_dm'):
        flash('DM login required.')
        return redirect(url_for('dm_home'))

    post_id = request.form.get('post_id', '')
    global posts
    deleted = next((p for p in posts if p.get('id') == post_id), None)
    posts = [p for p in posts if p.get('id') != post_id]
    save_posts()
    if deleted:
        record_post_deletion(post_id)

    if deleted:
        author = 'DM' if deleted.get('is_dm') else deleted.get('username', 'unknown')
        snippet = deleted.get('message', '')
        snippet = snippet if len(snippet) <= 80 else snippet[:77] + '...'
        log_activity('DM', 'DELETED_MESSAGE', f'author={author}, post_id={post_id}, message="{snippet}"')

    return redirect(url_for('dm_home'))


# ---------------------------------------------------------------------------
# Routes: DM Players window (roster + one character's editor)
# ---------------------------------------------------------------------------
def back_to_editor():
    """Where every DM character form returns to: that character's editor in
    the Players window, or the roster if the character is gone."""
    if not session.get('is_dm'):
        return redirect(url_for('dm_home'))
    char_id = request.form.get('character_id', '')
    if char_id in characters:
        return redirect(url_for('dm_player', character_id=char_id))
    return redirect(url_for('dm_players'))


STALE_SECTION_NAMES = {'stats': 'stats', 'kit': 'kit', 'inventory': 'inventory'}


def stale_redirect(character, section):
    log_activity('DM', 'EDIT_CONFLICT', f'character={character["name"]}, section={section}')
    flash(f'{character["name"]}\'s {STALE_SECTION_NAMES[section]} changed after you opened this '
          f'(the player edited it). Nothing was saved — this is the latest version, so redo your change.')
    return back_to_editor()


def dm_character_view(character):
    return {**character, **roster_row(character),
            'effective': effective_abilities(character),
            'conditions': public_conditions(character)}


@app.route('/dm/players')
def dm_players():
    if not session.get('is_dm'):
        return redirect(url_for('dm_home'))
    return render_cached(
        _DM_PLAYERS_TPL,
        character=None,
        roster=[roster_row(c) for c in characters.values()],
        min_hp=MIN_HP,
    )


@app.route('/dm/players/state')
def dm_players_state():
    """Polled by the Players window to keep the roster live and to warn an
    open editor when the player changes something underneath it."""
    if not session.get('is_dm'):
        return jsonify({'error': 'DM login required.'}), 403
    return jsonify({'characters': [roster_row(c) for c in characters.values()]})


@app.route('/dm/players/quick', methods=['POST'])
def dm_quick_adjust():
    """Roster +/- buttons for HP and omens. These are relative nudges, so
    they apply on top of whatever the current value is — no conflict check
    needed. HP follows the rules: it can't be healed past max, and going
    below 0 kills (the page confirms that first)."""
    if not session.get('is_dm'):
        return jsonify({'error': 'DM login required.'}), 403
    data = request.get_json(silent=True)
    if not isinstance(data, dict):
        return jsonify({'error': 'Invalid request.'}), 400
    character = characters.get(data.get('character_id'))
    field = data.get('field')
    delta = data.get('delta')
    if not character:
        return jsonify({'error': 'Character not found.'}), 404
    if field not in ('hp', 'omens') or isinstance(delta, bool) or delta not in (-1, 1):
        return jsonify({'error': 'Invalid adjustment.'}), 400
    if character.get('dead'):
        return jsonify({'error': f'{character["name"]} is dead.'}), 403

    old = character.get(field, 0)
    if field == 'hp':
        ceiling = max(character.get('max_hp', 0), old)
        new = max(MIN_HP, min(ceiling, old + delta))
    else:
        new = max(0, min(99, old + delta))

    if new != old:
        character[field] = new
        died = field == 'hp' and new < 0
        if died:
            character['dead'] = True
        bump(character, 'vitals')
        save_characters()
        log_activity('DM', 'QUICK_ADJUST', f'character={character["name"]}, {field} {old}->{new}')
        if died:
            log_activity(character['name'], 'DIED', f'hp={new} (DM)')

    return jsonify({'ok': True, 'row': roster_row(character)})


@app.route('/dm/players/<character_id>')
def dm_player(character_id):
    if not session.get('is_dm'):
        return redirect(url_for('dm_home'))
    character = characters.get(character_id)
    if not character:
        flash('That character no longer exists.')
        return redirect(url_for('dm_players'))
    return render_cached(
        _DM_PLAYERS_TPL,
        character=dm_character_view(character),
        ability_pairs=ABILITY_PAIRS,
        slot_count=INVENTORY_SLOTS,
        container_presets=CONTAINER_PRESETS,
        max_container_slots=MAX_CONTAINER_SLOTS,
        max_containers=MAX_CONTAINERS,
        max_container_name=MAX_CONTAINER_NAME,
        max_item_len=MAX_ITEM_LENGTH,
        max_conditions=MAX_CONDITIONS,
        max_condition_name=MAX_CONDITION_NAME,
        max_condition_mod=MAX_CONDITION_MOD,
    )


@app.route('/dm/condition/add', methods=['POST'])
def dm_add_condition():
    """Apply a named temporary condition. Ability modifiers are optional: a
    condition with none is just a visible label (e.g. 'Blinded')."""
    character = dm_character_from_form()
    if not character:
        return back_to_editor()

    name = clean_text(request.form.get('name', ''), MAX_CONDITION_NAME)
    if not name:
        flash('A condition needs a name.')
        return back_to_editor()
    if len(character.get('conditions', [])) >= MAX_CONDITIONS:
        flash(f'{character["name"]} already has {MAX_CONDITIONS} conditions.')
        return back_to_editor()

    mods = {}
    for key in ABILITY_KEYS:
        raw = request.form.get(key, '').strip() or '0'
        try:
            value = int(raw)
        except ValueError:
            flash('Condition modifiers must be whole numbers.')
            return back_to_editor()
        if not -MAX_CONDITION_MOD <= value <= MAX_CONDITION_MOD:
            flash(f'Condition modifiers must be between -{MAX_CONDITION_MOD} and +{MAX_CONDITION_MOD}.')
            return back_to_editor()
        if value:
            mods[key] = value

    condition = {'id': secrets.token_hex(4), 'name': name, 'mods': mods}
    character.setdefault('conditions', []).append(condition)
    bump(character, 'conditions')
    save_characters()
    summary = condition_summary(condition)
    log_activity('DM', 'CONDITION_APPLIED', f'character={character["name"]}, {name}' + (f' ({summary})' if summary else ''))
    return back_to_editor()


@app.route('/dm/condition/remove', methods=['POST'])
def dm_remove_condition():
    character = dm_character_from_form()
    if not character:
        return back_to_editor()
    cond_id = request.form.get('condition_id', '')
    condition = next((c for c in character.get('conditions', []) if c['id'] == cond_id), None)
    if not condition:
        flash('That condition was already removed.')
        return back_to_editor()

    character['conditions'].remove(condition)
    bump(character, 'conditions')
    save_characters()
    log_activity('DM', 'CONDITION_REMOVED', f'character={character["name"]}, {condition["name"]}')
    return back_to_editor()


@app.route('/dm/update-stats', methods=['POST'])
def dm_update_stats():
    if not session.get('is_dm'):
        flash('DM login required.')
        return back_to_editor()

    char_id = request.form.get('character_id', '')
    character = characters.get(char_id)
    if not character:
        flash('Character not found.')
        return back_to_editor()

    fields = {
        'agility': (MIN_ABILITY, MAX_ABILITY),
        'presence': (MIN_ABILITY, MAX_ABILITY),
        'strength': (MIN_ABILITY, MAX_ABILITY),
        'toughness': (MIN_ABILITY, MAX_ABILITY),
        'hp': (MIN_HP, MAX_HP),
        'max_hp': (1, MAX_HP),
        'omens': (0, 99),
        'silver': (0, MAX_SILVER),
    }

    if not (rev_matches(character, 'vitals', request.form.get('rev_vitals'))
            and rev_matches(character, 'abilities', request.form.get('rev_abilities'))):
        return stale_redirect(character, 'stats')

    try:
        new_stats = {key: int(request.form.get(key, '')) for key in fields}
    except ValueError:
        flash('Stat values must be whole numbers.')
        return back_to_editor()

    for key, (lo, hi) in fields.items():
        if not (lo <= new_stats[key] <= hi):
            flash(f'{key} must be between {lo} and {hi}.')
            return back_to_editor()

    old_stats = {k: character.get(k) for k in new_stats}
    character.update(new_stats)
    if any(old_stats[k] != new_stats[k] for k in ABILITY_KEYS):
        bump(character, 'abilities')
    if any(old_stats[k] != new_stats[k] for k in new_stats if k not in ABILITY_KEYS):
        bump(character, 'vitals')
    save_characters()

    diffs = [f'{k} {old_stats[k]}->{new_stats[k]}' for k in new_stats if old_stats[k] != new_stats[k]]
    if diffs:
        log_activity('DM', 'UPDATED_STATS', f'character={character["name"]}, ' + ', '.join(diffs))

    return back_to_editor()


@app.route('/dm/update-kit', methods=['POST'])
def dm_update_kit():
    """Weapon and armor are free text so the DM can hand out anything the
    tables never thought of. Containers have their own routes below."""
    if not session.get('is_dm'):
        flash('DM login required.')
        return back_to_editor()

    char_id = request.form.get('character_id', '')
    character = characters.get(char_id)
    if not character:
        flash('Character not found.')
        return back_to_editor()

    if not rev_matches(character, 'kit', request.form.get('rev_kit')):
        return stale_redirect(character, 'kit')

    try:
        tier = int(request.form.get('armor_tier', '0'))
    except ValueError:
        tier = 0
    tier = max(0, min(3, tier))

    new_kit = {
        'weapon': clean_text(request.form.get('weapon', ''), MAX_ITEM_LENGTH) or 'Unarmed (d2)',
        'armor': clean_text(request.form.get('armor', ''), MAX_ITEM_LENGTH) or ARMOR[0][0],
        'armor_tier': tier,
    }

    diffs = [f'{k} "{character.get(k)}"->"{v}"' for k, v in new_kit.items() if character.get(k) != v]
    character.update(new_kit)
    if diffs:
        bump(character, 'kit')
    save_characters()

    if diffs:
        log_activity('DM', 'UPDATED_KIT', f'character={character["name"]}, ' + ', '.join(diffs))

    return back_to_editor()


def dm_character_from_form():
    """Shared guard for the DM inventory/container routes: returns the
    character, or None after flashing why."""
    if not session.get('is_dm'):
        flash('DM login required.')
        return None
    character = characters.get(request.form.get('character_id', ''))
    if not character:
        flash('Character not found.')
    return character


def find_container(character, container_id):
    return next((c for c in character.get('containers', []) if c['id'] == container_id), None)


def container_fields_from_form():
    """(name, capacity) from the add/edit container forms, or None."""
    name = clean_text(request.form.get('name', ''), MAX_CONTAINER_NAME)
    try:
        capacity = int(request.form.get('capacity', ''))
    except ValueError:
        return None
    if not name or not (1 <= capacity <= MAX_CONTAINER_SLOTS):
        return None
    return name, capacity


@app.route('/dm/update-inventory', methods=['POST'])
def dm_update_inventory():
    character = dm_character_from_form()
    if not character:
        return back_to_editor()

    if not rev_matches(character, 'inventory', request.form.get('rev_inventory')):
        return stale_redirect(character, 'inventory')

    new_person = fit_items(request.form.getlist('slot'), INVENTORY_SLOTS)
    new_free = fit_items([request.form.get('free', '')], 1)[0]
    new_containers = {
        c['id']: fit_items(request.form.getlist('c-' + c['id']), c['capacity'])
        for c in character.get('containers', [])
    }

    changes = inventory_changes(character, new_person, new_containers, new_free)
    character['inventory'] = new_person
    character['free_item'] = new_free
    for c in character.get('containers', []):
        c['items'] = new_containers[c['id']]
    if changes:
        bump(character, 'inventory')
    save_characters()

    if changes:
        log_activity('DM', 'INVENTORY_UPDATED', f'character={character["name"]}; ' + '; '.join(changes))

    return back_to_editor()


@app.route('/dm/container/add', methods=['POST'])
def dm_add_container():
    character = dm_character_from_form()
    if not character:
        return back_to_editor()

    fields = container_fields_from_form()
    if not fields:
        flash(f'A container needs a name and 1–{MAX_CONTAINER_SLOTS} slots.')
        return back_to_editor()
    if len(character['containers']) >= MAX_CONTAINERS:
        flash(f'{character["name"]} already has {MAX_CONTAINERS} containers.')
        return back_to_editor()

    container = new_container(*fields)
    character['containers'].append(container)
    bump(character, 'inventory')
    save_characters()
    log_activity('DM', 'ADDED_CONTAINER',
                 f'character={character["name"]}, {container["name"]} ({container["capacity"]})')
    return back_to_editor()


@app.route('/dm/container/update', methods=['POST'])
def dm_update_container():
    character = dm_character_from_form()
    if not character:
        return back_to_editor()
    container = find_container(character, request.form.get('container_id', ''))
    fields = container_fields_from_form()
    if not container or not fields:
        flash(f'A container needs a name and 1–{MAX_CONTAINER_SLOTS} slots.')
        return back_to_editor()

    name, capacity = fields
    # Never silently throw items away by shrinking a container.
    stranded = [i + 1 for i, item in enumerate(container['items'][capacity:], start=capacity) if item.strip()]
    if stranded:
        flash(f'Empty {container["name"]} slot(s) {", ".join(map(str, stranded))} '
              f'before shrinking it to {capacity}.')
        return back_to_editor()

    old = f'{container["name"]} ({container["capacity"]})'
    container['name'] = name
    container['capacity'] = capacity
    container['items'] = fit_items(container['items'], capacity)
    bump(character, 'inventory')
    save_characters()
    log_activity('DM', 'UPDATED_CONTAINER', f'character={character["name"]}, {old} -> {name} ({capacity})')
    return back_to_editor()


@app.route('/dm/container/remove', methods=['POST'])
def dm_remove_container():
    """Losing a container loses everything in it — that's the point."""
    character = dm_character_from_form()
    if not character:
        return back_to_editor()
    container = find_container(character, request.form.get('container_id', ''))
    if not container:
        flash('Container not found.')
        return back_to_editor()

    character['containers'].remove(container)
    bump(character, 'inventory')
    save_characters()
    lost = [i for i in container['items'] if i.strip()]
    log_activity('DM', 'REMOVED_CONTAINER',
                 f'character={character["name"]}, {container["name"]}, lost: ' + ('; '.join(lost) or 'nothing'))
    flash(f'{character["name"]} lost the {container["name"]}' + (f' and {len(lost)} item(s) in it.' if lost else '.'))
    return back_to_editor()


@app.route('/dm/toggle-dead', methods=['POST'])
def dm_toggle_dead():
    if not session.get('is_dm'):
        flash('DM login required.')
        return back_to_editor()

    char_id = request.form.get('character_id', '')
    character = characters.get(char_id)
    if not character:
        flash('Character not found.')
        return back_to_editor()

    character['dead'] = not character.get('dead', False)
    # A revived character sitting on negative HP would immediately die again
    # the next time their sheet autosaves, so pull them back to 0 (broken).
    if not character['dead'] and character.get('hp', 0) < 0:
        character['hp'] = 0
    bump(character, 'vitals')
    save_characters()

    action = 'MARKED_DEAD' if character['dead'] else 'REVIVED'
    log_activity('DM', action, f'character={character["name"]}')

    return back_to_editor()


@app.route('/dm/delete-character', methods=['POST'])
def dm_delete_character():
    """Remove a character for good. Their posts are left in the feed — the
    game happened, and deleting a retired scvm shouldn't punch holes in the
    story. Any whisper aimed at them simply stops matching a character and
    drops out of every player's feed."""
    if not session.get('is_dm'):
        flash('DM login required.')
        return back_to_editor()

    char_id = request.form.get('character_id', '')
    character = characters.get(char_id)
    if not character:
        flash('Character not found.')
        return back_to_editor()

    name = character['name']

    # Drop any not-yet-converted legacy browser link. Browsers logged in
    # with this character's password are signed out by get_character() on
    # their next request, since the character no longer exists.
    for cid in [cid for cid, chid in client_map.items() if chid == char_id]:
        del client_map[cid]

    del characters[char_id]
    save_characters()

    log_activity('DM', 'DELETED_CHARACTER', f'character={name}, id={char_id}')
    flash(f'{name} has been deleted.')

    return back_to_editor()


@app.route('/dm/reset-login', methods=['POST'])
def dm_reset_login():
    """Give a character a fresh password. Every browser currently logged in
    as them is signed out on its next request (login_version changes)."""
    if not session.get('is_dm'):
        flash('DM login required.')
        return back_to_editor()

    char_id = request.form.get('character_id', '')
    character = characters.get(char_id)
    if not character:
        flash('Character not found.')
        return back_to_editor()

    character['password'] = generate_password()
    character['login_version'] = character.get('login_version', 1) + 1
    for cid in [cid for cid, chid in client_map.items() if chid == char_id]:
        del client_map[cid]
    save_characters()

    log_activity('DM', 'RESET_LOGIN', f'character={character["name"]}')
    flash(f'{character["name"]} has a new password and every browser using the old one was signed out.')
    return back_to_editor()


# ---------------------------------------------------------------------------
# Routes: player login / logout
# ---------------------------------------------------------------------------
@app.route('/login', methods=['POST'])
def player_login():
    ip = request.remote_addr or 'unknown'
    if login_throttled(ip):
        flash('Too many failed logins. Wait a few minutes and try again.')
        return redirect(url_for('index'))

    username = request.form.get('username', '')[:MAX_LOGIN_FIELD_LENGTH]
    password = request.form.get('password', '')[:MAX_LOGIN_FIELD_LENGTH]
    character = find_character_by_username(username)

    # compare_digest on both branches keeps response timing from revealing
    # whether the username exists.
    expected = character['password'] if character else generate_password()
    if character and secrets.compare_digest(password.encode('utf-8'), expected.encode('utf-8')):
        _login_failures.pop(ip, None)
        log_in_as(character)
        log_activity(character['name'], 'LOGIN_SUCCESS', f'ip={ip}')
        return redirect(url_for('index'))

    secrets.compare_digest(password.encode('utf-8'), expected.encode('utf-8'))
    _login_failures.setdefault(ip, []).append(datetime.now())
    log_activity(clean_text(username, MAX_LOGIN_FIELD_LENGTH) or '?', 'LOGIN_FAILED', f'ip={ip}')
    flash('Wrong username or password.')
    return redirect(url_for('index'))


@app.route('/logout', methods=['POST'])
def player_logout():
    character = get_character()
    log_out_player()
    if character:
        log_activity(character['name'], 'LOGOUT')
    return redirect(url_for('index'))


# Old claim links still resolve, but only to explain where they went.
@app.route('/claim/<character_id>', methods=['GET', 'POST'])
def claim_character(character_id):
    flash('Claim links have been replaced by logins. Ask the DM for your username and password.')
    return redirect(url_for('index'))


if __name__ == '__main__':
    # debug=True is left off here on purpose: its auto-reloader runs a
    # background filesystem watcher that costs real CPU on a Pi, and its
    # interactive debugger is a code-execution risk on any network-reachable
    # host. Flip it on temporarily only while you're actively editing app.py,
    # e.g.: app.run(debug=True, host='0.0.0.0')
    #
    # threaded=True lets the server handle the page load and its background
    # AJAX calls (dice rolls, inventory autosave) concurrently instead of
    # queuing them one at a time.
    app.run(host=os.environ.get('MORKBORG_HOST', '0.0.0.0'),
            port=int(os.environ.get('MORKBORG_PORT', '5000')),
            threaded=True)
