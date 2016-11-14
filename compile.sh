#!/bin/bash

#../../.cabal-sandbox/bin/hastec Main.hs -o main.js \
hastec Main.hs -o main.js \
  -Wall \
  --outdir=../../dist/js \
  --debug 
#  -fwarn-unused-imports \
#  -fwarn-unused-matches 
#  -fwarn-unused-binds 
  
#../../.cabal-sandbox/bin/hastec -fwarn-incomplete-patterns Main.hs -o main.js --outdir=../../dist/js --debug
rm *.hi *.o FormStructure/*.o FormStructure/*.hi FormStructure/*.jsmod FormElement/*.o FormElement/*.hi FormElement/*.jsmod
mv main.js ../../elixir-questionnaire/static/js