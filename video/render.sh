#!/bin/sh
# SPDX-License-Identifier: CC0-1.0
#
# Render the scenes and join them into one video.
#   ./render.sh [l|m|h|k] [Scene ...]
# Quality l = 480p15 (preview), m = 720p30, h = 1080p60, k = 2160p60. Default h.
# Scenes render 4 at a time; the joined file is out/zzn_explainer_<quality>.mp4.
#
set -e
cd "$(dirname "$0")"
Q=${1:-h}
[ $# -gt 0 ] && shift
PY=${MANIM_PY:-$HOME/claude/venvs/manim/bin/python}
SCENES=${*:-$($PY -c "import scenes; print(' '.join(scenes.SCENES))")}
mkdir -p out logs
for s in $SCENES; do echo $s; done | \
  xargs -P 4 -I{} sh -c "$PY -m manim render -q$Q --disable_caching scenes.py {} > logs/{}.$Q.log 2>&1 && echo done {} || echo FAILED {}"
case $Q in
  l) D=480p15 ;; m) D=720p30 ;; h) D=1080p60 ;; k) D=2160p60 ;;
esac
ALL=$($PY -c "import scenes; print(' '.join(scenes.SCENES))")

# Each scene's narration ends before its video does. Pad (or, without narration, add) a
# silent audio track to the video's length, so the joined narration stays in sync.
#
mkdir -p out/pad
: > out/list.txt
for s in $ALL; do
  f=media/videos/scenes/$D/$s.mp4
  [ -f "$f" ] || continue
  p=out/pad/${s}_$Q.mp4
  if ffprobe -v error -select_streams a -show_entries stream=index -of csv=p=0 "$f" | grep -q .; then
    ffmpeg -y -loglevel error -i "$f" -c:v copy -af apad -c:a aac -ar 48000 -ac 2 -b:a 192k -shortest "$p"
  else
    ffmpeg -y -loglevel error -i "$f" -f lavfi -i anullsrc=r=48000:cl=stereo -c:v copy -c:a aac -b:a 192k -shortest "$p"
  fi
  echo "file 'pad/${s}_$Q.mp4'" >> out/list.txt
done
ffmpeg -y -loglevel error -f concat -safe 0 -i out/list.txt -c copy out/zzn_explainer_$Q.mp4
echo "out/zzn_explainer_$Q.mp4"
