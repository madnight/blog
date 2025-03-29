edge-tts --voice en-US-EricNeural --file input.txt --write-media out.mp3 
ffmpeg -y -i out.mp3 -codec:a libmp3lame -b:a 192k -ar 44100 output_cbr.mp3
