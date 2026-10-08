#!/bin/bash

echo "creating ../../demo/js/web_zzn.js"
browserify --standalone zzn zzn.js > ../../demo/js/web_zzn.js
