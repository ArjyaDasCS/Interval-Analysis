#!/usr/bin/env bash

set -e

source environ.sh
echo === building targets

cd target1-pub;   javac -target 8 -g *.java;  cd ..
cd target2-mine;  javac -target 8 -g *.java;  cd ..


