#!/bin/sh

lein clean
lein deps
lein test
script/build-docs.sh
