# MÖRK BORG Message Board

A small self-hosted play-by-post table for MÖRK BORG (Bare Bones Edition).
Players roll up a scvm in the browser, keep their sheet on screen, post to a
shared feed and roll dice into their posts. The DM gets a password-protected
dashboard for running the game, plus the rules and adventures in pop-out
windows.

Everything runs from a single `app.py`, with no external services. All game
state is stored in one SQLite file in the `data/` folder. SQLite is built into
Python, so there's no database server to run.

---

## What's in the box

**For players**
- Character creation with the six optional classes or the classless build.
  Each class shows a bullet summary of what it gives you before you pick it,
  then drives the rolls: HP, silver and Omen dice, ability modifiers, weapon
  and armor dice, origin and starting gear.
- A generated username and password per character, so a player can log back
  in from any browser.
- A live character sheet. HP, Omens, silver and inventory save as you type,
  with a carrying-capacity readout. Negative HP marks the character dead.
- A message feed that updates every few seconds without a reload, with
  `*bold*`, `"italic dialogue"` and `@Name` mentions in each character's colour.
- A dice roller that attaches labelled rolls to a post. Every die is rolled and
  re-checked on the server, so totals can't be edited in the browser.

**For the DM**
- Post as the DM, or whisper privately to one character — whispers never
  appear in anyone else's feed or API responses.
- Edit any character's abilities, HP, Omens, silver, kit and inventory.
- See and reset each character's login.
- Mark characters dead or revive them.
- Set the scene name shown in everyone's banner.
- Download a zip backup of all game state, or import one.
- Pop-out buttons for the rules and each adventure.

---

## Project layout

```
morkapp/
    app.py               the whole application
    requirements.txt     Python dependencies (Flask, waitress)
    Dockerfile           builds an image containing only app.py + dependencies
    docker-compose.yml   runs it: port, .env, and the ./data bind mount
    .dockerignore        keeps data/, .env and old files out of the image
    .env                 your secrets — never commit or share (see below)
    .env.example         template for .env
    data/                everything the app reads or writes
        rules/
            MORK_BORG_BARE_BONES_EDITION.md   served by the Rules pop-out
            MÖRK BORG BARE BONES EDITION.pdf  kept for reference, not served
        adventures/
            path-of-the-penitent.html
            rotblack-sludge.html
            two-guillians.html
        morkborg.db (+ -wal, -shm)  game state + activity log (SQLite, created at runtime)
        backups/                    automatic pre-import snapshots
        legacy-json/                old JSON files, moved here once imported
```

The image holds only code. The `data/` folder is bind-mounted into the
container at `/app/data`, so game state, rules and adventures all live on the
host and survive rebuilds.

---

## Configuration (.env)

The app reads its secrets from environment variables and **refuses to start**
if either required one is missing — there are no built-in defaults.

| Variable | Required | Purpose |
|---|---|---|
| `MORKBORG_SECRET_KEY` | yes | Signs session cookies. Changing it signs everyone out. |
| `MORKBORG_DM_PASSWORD` | yes | The shared DM password. |
| `PUID` / `PGID` | no | Host user/group the container runs as; must own `data/`. Default `1000`. |
| `TZ` | no | Timezone for activity-log timestamps (e.g. `America/New_York`). |
| `MORKBORG_BEHIND_PROXY` | no | Set to `1` only behind a reverse proxy, so login limits see real client IPs. |
| `MORKBORG_DATA_DIR` | no | Where `data/` lives. Defaults to `data/` next to `app.py`; the Dockerfile sets `/app/data`. |
| `MORKBORG_HOST` / `MORKBORG_PORT` | no | Bind address for a plain `python3 app.py` run only (default `0.0.0.0:5000`). |

Docker Compose loads `.env` via `env_file:`. A plain `python3 app.py` run also
reads `.env` from next to `app.py`. Real environment variables win over `.env`.

To create a fresh `.env`:

```bash
cp .env.example .env
```

then generate a key and paste it in:

```bash
python3 -c "import secrets; print(secrets.token_hex(32))"
```

Change `MORKBORG_DM_PASSWORD` from `change-me` before anyone else can reach
the machine.

---

## Running with Docker (recommended)

**1. Copy the folder to the Linux host**, including `data/` and `.env`.

**2. Make `data/` writable by the container.** The image creates no user
account. Compose runs the container as `PUID:PGID` from `.env`, so it writes
to `data/` as you. Set those to your own IDs (`id -u` and `id -g`), then make
sure you own `data/` and can write to it, from the folder that holds
`docker-compose.yml`:

```bash
sudo chown -R "$(id -u):$(id -g)" data && chmod -R u+rwX data
```

**3. Build and start:**

```bash
docker compose up -d --build
```

The board is at `http://<host>:999/`. Change the left side of `"999:5000"` in
`docker-compose.yml` to use a different port.

**4. Check it:**

```bash
docker compose logs -f
```

The first log line shows the data directory in use (`/app/data`). If the
folder isn't writable the app exits immediately with a clear message rather
than silently losing saves.

After editing `app.py`, rebuild with `docker compose up -d --build`. After
editing `.env`, run `docker compose up -d` so the container is recreated with
the new values (a plain restart does not re-read `env_file`).

---

## Running without Docker

```bash
python3 -m venv .venv
.venv/bin/pip install -r requirements.txt
.venv/bin/python app.py
```

It listens on port 5000 on every interface, using `.env` and `data/` next to
`app.py`. For anything longer than a test session, run it under waitress the
way the container does:

```bash
.venv/bin/python -m waitress --host=0.0.0.0 --port=5000 --threads=8 app:app
```

---

## Files in data/

All game state lives in one SQLite database, `data/morkborg.db`, created on
first start.

| Path | Holds |
|---|---|
| `morkborg.db` | Everything: posts (including whispers), characters and their logins, scene name, DM notes, and the activity log |
| `morkborg.db-wal`, `morkborg.db-shm` | SQLite's working files. They belong to `morkborg.db`; never delete or copy one without the others |
| `backups/` | Automatic zip snapshots of the game, saved before each backup import |
| `legacy-json/` | The old JSON files and `Activity Log.txt`, moved here after being imported (see below) |

Inside the database:

| Table | Holds |
|---|---|
| `posts` | One row per post. The whole post is JSON in `data`; `seq`, author, whisper target etc. are copied into columns for querying |
| `characters` | One row per character, likewise: whole sheet in `data`, plus `username`, `name`, `dead` |
| `activity_log` | Append-only audit trail of every player and DM action (`ts`, `actor`, `action`, `details`) |
| `meta` | Scene name, DM notes, schema version and the backup-import epoch |
| `client_map` | Legacy browser links from before logins; empties itself over time |

You can browse it with `sqlite3 data/morkborg.db` or DB Browser for SQLite,
even while the app is running. Don't edit it while the app is running: the
app keeps the game in memory and would overwrite your change.

**Backing up.** The **Download backup** link on the DM dashboard gives a zip
of readable JSON files plus the activity log as text. It's the same format the
app used before it switched to SQLite, so old and new backups both import.
Copying `data/` works too, but only while the app is stopped
(`docker compose stop`). A copy of a live database can miss its newest
changes.

**Starting fresh.** Stop the app and move `morkborg.db`, `morkborg.db-wal`
and `morkborg.db-shm` out of `data/`. Leave `rules/` and `adventures/` in
place.

**Upgrading from the JSON version.** On the first start after upgrading, any
`Characters.json`, `Hidden Message Board.json`, `Scene.json`, `DMNotes.json`
and `Activity Log.txt` in `data/` are imported in one go, then moved into
`data/legacy-json/<date-time>/`. Nothing is deleted. If one of them is
damaged, the app refuses to start and imports nothing, the same as before.
Once you're happy the game looks right, you can delete `legacy-json/`.

---

## Adventures and rules

The Rules pop-out serves the Markdown file in `data/rules/`. Any of these
filenames works: `MORK_BORG_BARE_BONES_EDITION.md`,
`MÖRK_BORG_BARE_BONES_EDITION.md`, `MÖRK BORG BARE BONES EDITION.md`,
`rules.md`. The rendered rules are cached, so restart after editing the file.
The PDF alongside it is for your reference; the app doesn't serve it.

Drop any `.html` or `.md` file into `data/adventures/` and reload the DM page —
it gets picked up automatically and given its own pop-out button, named after
the filename. `.html` files keep their own styling; `.md` files are rendered
with the same skin as the rules page. `<script>` tags are stripped from
adventure HTML on the way out, since those pages run on the app's own origin.

**Rotblack Sludge** is included as a 16-page handout built from the PDF, cover
omitted. The map, illustrations and webfonts are embedded in the file, so it
renders with no internet connection and makes no external requests.

---

## Playing over the internet

The DM has one shared password; players log in with generated per-character
credentials. That is fine on a home network and **not** something to expose
directly to the open internet. Don't forward the port from your router.

To play with people elsewhere, put them on a private network with you instead:

- **Tailscale** or another WireGuard mesh is the easiest option. Install it on
  the host and on each player's machine, and they reach the board at the
  host's Tailscale address with nothing exposed publicly.
- A **reverse proxy with HTTPS and its own authentication** (Caddy, or nginx
  with basic auth) also works if you already run one. Set
  `MORKBORG_BEHIND_PROXY=1` in `.env` when you do.

Whichever you use, serve it over HTTPS if it crosses the public internet —
the session cookie is what keeps a player logged in.

---

## Day-to-day use

**Giving a character to a player.** Each character's username and password
are on the DM dashboard. Read them out or send them; the player logs in from
the front page. Old claim links now just explain that logins replaced them.

**A player lost their character.** Clearing site data, switching browsers or
using a private window logs them out. Their character is not gone — they log
in again with their username and password, which the DM can look up or reset.

**Death.** Negative HP marks a character dead automatically; 0 HP shows a
Broken banner instead. A dead player sees a death screen and can roll up a
replacement. The dead character stays on the DM dashboard permanently, and the
DM can revive anyone from there.

---

## Notes and limits

- Player posts are capped at 300 characters; DM posts are uncapped. Request
  bodies over 64KB are rejected, except backup imports.
- Player sessions last a year, so people stay logged in between sessions.
- The app's own pages load two fonts from Google Fonts. Without internet the
  layout still works, it just falls back to Impact and Arial Narrow.
- The activity log only grows, and a backup import doesn't clear it: it covers
  every game the board has run. A line is about 100 bytes, so even years of
  play stay small.
- MÖRK BORG is copyright Ockult Örtmästare Games and Stockholm Kartell. This
  is a personal tool for your own table, not affiliated with or endorsed by
  them.
