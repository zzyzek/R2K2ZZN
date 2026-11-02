# Explainer video

A Manim video (about 12 minutes, 1080p60, narrated, with on-screen captions) explaining two-colour
Zig-Zag Numberlink on rectangles: the problem, the plug DP for thin grids, the catalogue, the
reductions and band extension, the moves, a worked example, and the proof and its Lean check.

Every instance, solution, cut and trace in the video is computed by the Python library in
[`lib/python`](../lib/python) and checked with `check_solution` or `fires` ([`data.py`](data.py)).

| File | Contents |
|---|---|
| [`data.py`](data.py) | The instances and solutions shown, computed by the library (`python3 data.py` prints a summary) |
| [`gridview.py`](gridview.py) | Drawing helpers: grid, endpoints, paths, cuts, captions |
| [`scenes.py`](scenes.py) | One Manim scene per section (`SCENES` lists the order) |
| [`render.sh`](render.sh) | Renders the scenes, 4 at a time, and joins them into `out/zzn_explainer_<q>.mp4` |

## Rendering

Needs [Manim Community](https://www.manim.community/) 0.22, LaTeX (for endpoint labels) and
ffmpeg. On Debian/Ubuntu: `apt install python3-venv python3-dev pkg-config libcairo2-dev
libpango1.0-dev ffmpeg texlive`, then `python3 -m venv venv && venv/bin/pip install manim`.

```bash
MANIM_PY=venv/bin/python ./render.sh l              # 480p15 preview, about 1 minute
MANIM_PY=venv/bin/python ./render.sh h              # 1080p60, about 20 minutes on 4 cores
MANIM_PY=venv/bin/python ./render.sh l S08Band      # one scene
```

## Narration

Each caption is spoken by [Kokoro](https://github.com/thewh1teagle/kokoro-onnx) (`pip install
kokoro-onnx soundfile`, plus the model files `kokoro-v1.0.onnx` and `voices-v1.0.bin` from its
releases). `gridview.spoken` rewrites a caption for speech (s₀ as "s zero", × as "by", and so on);
the audio is synthesised on first use and cached in `audio/`, and each caption stays on screen for
its audio's length. Environment variables: `ZZN_NARRATE=0` (captions only, timed by reading
length), `ZZN_VOICE` (default `af_river:0.5+am_liam:0.5`, a 50/50 blend), `ZZN_SPEED` (speech rate, default 1.07), `ZZN_KOKORO` (model directory, default
`~/claude/models/kokoro`).

## License

CC0 1.0 Universal, like the rest of the repository. See [`LICENSE`](../LICENSE).
