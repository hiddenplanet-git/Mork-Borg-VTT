# syntax=docker/dockerfile:1
#
# MÖRK BORG board image. Holds only the code: app.py and its Python
# dependencies. Everything else comes in at runtime from docker-compose.yml:
#   - secrets (MORKBORG_SECRET_KEY, MORKBORG_DM_PASSWORD) from .env
#   - game state, rules and adventures from the ./data bind mount at /app/data

FROM python:3.12-slim

# PYTHONUNBUFFERED so log lines reach `docker compose logs` immediately rather
# than sitting in a buffer; PYTHONDONTWRITEBYTECODE to keep __pycache__ out of
# the image. MORKBORG_DATA_DIR is where app.py looks for data/ — it matches
# the bind-mount target in docker-compose.yml.
ENV PYTHONUNBUFFERED=1 \
    PYTHONDONTWRITEBYTECODE=1 \
    PIP_NO_CACHE_DIR=1 \
    MORKBORG_DATA_DIR=/app/data

WORKDIR /app

# Dependencies first, so editing app.py doesn't invalidate the pip layer.
COPY requirements.txt ./
RUN pip install --no-cache-dir -r requirements.txt

COPY app.py ./

# Don't run as root, but don't create a user inside the image either. A
# numeric USER needs no account, and the app only writes to /app/data,
# which is your own bind-mounted ./data folder. docker-compose.yml replaces
# this with PUID:PGID from .env, so the container writes as *you* and the
# files in ./data stay owned by you on the host. 1000:1000 is only the
# fallback for running the image without compose.
USER 1000:1000

# The app listens on 5000 inside the container. The published port on the host
# is set in docker-compose.yml; nothing here needs to change to move it.
EXPOSE 5000

# Plain urllib rather than curl, which isn't in the slim image.
HEALTHCHECK --interval=30s --timeout=5s --start-period=10s --retries=3 \
    CMD ["python", "-c", "import urllib.request as u, sys; sys.exit(0 if u.urlopen('http://127.0.0.1:5000/', timeout=4).status == 200 else 1)"]

# Waitress rather than Flask's development server: it's a real WSGI server,
# handles concurrent requests properly and doesn't print a scary warning.
CMD ["python", "-m", "waitress", "--host=0.0.0.0", "--port=5000", "--threads=8", "app:app"]
