# Pitch Guesser — web deployment

This is a web-hostable version of the uploaded Pitch Guesser app. It keeps the existing HTML/JavaScript interface and Python game logic, installs FFmpeg in the container, listens on Render's public port, and isolates game state by browser session.

## Season range

The season selector is restricted to 2021 and later. “All years” randomly selects from 2021 onward.

## Deploy to Render

1. Create a GitHub repository and upload the contents of this folder (`app.py`, `Dockerfile`, `requirements.txt`, `render.yaml`).
2. In Render, choose **New → Blueprint** and connect that repository.
3. Render reads `render.yaml`, builds the Docker image, and gives you a public `onrender.com` URL.
4. Open the URL and test a complete game.

The app retrieves pitch data and video from MLB Baseball Savant / MLB Stats API at runtime. Availability and response times therefore depend on those services. The first round can take a while because it searches for a suitable pitch and downloads its video.

## Run locally

Requires Docker:

```bash
docker build -t pitch-guesser .
docker run --rm -p 8000:8000 -e PORT=8000 pitch-guesser
```

Then open http://localhost:8000.

## Notes

- Each browser gets an independent game session; visitors no longer overwrite one another's active round or score.
- The existing game uses temporary video files and a local cache. On Render's free ephemeral filesystem, caches and personal-best files can be reset when the service restarts or redeploys.
- No MLB data or video is bundled; the game fetches it when played. Respect the source services' terms and availability.
