#!/bin/sh

working_path=$(pwd)
cd ..
parent_path=$(pwd)
cd $working_path

rm -rf gh-pages-temp
mkdir gh-pages-temp
mkdir gh-pages-temp/downloads

cd $parent_path
make html
cd $working_path

cp folders.css gh-pages-temp/
cp index.html gh-pages-temp/
cp -R ../html gh-pages-temp/

ghp-import gh-pages-temp -np
