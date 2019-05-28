virtualenv --python=python3 venv
source venv/bin/activate
pip install -r compileUtils/requirements.txt
find . -iname '*.ml' -or -iname '*.mli' | depgraph > depend.dot
mkdir customlib
cp compileUtils/dune customlib/dune
python compileUtils/makeCopyScript.py
sh moveScript.sh