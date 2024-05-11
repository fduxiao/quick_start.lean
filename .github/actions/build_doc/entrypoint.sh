#!/bin/sh
git config --global --add safe.directory $PWD

lake -R -Kenv=dev update
lake -R -Kenv=dev build QuickStart:docs
