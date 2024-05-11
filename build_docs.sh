#!/bin/sh
rm -r .lake/build/doc/*
DOCGEN_SRC="file" lake -R -Kenv=dev build QuickStart:docs
