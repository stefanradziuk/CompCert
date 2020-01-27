rm -rf customlib
make clean
esy ./configure x86_64-macosx
esy make -j 4
sh compileUtils/moveFiles.sh
