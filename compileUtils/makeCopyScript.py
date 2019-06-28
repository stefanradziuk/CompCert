import pydot as pd
import networkx as nx
import glob
import os


Gtmp = pd.graph_from_dot_file('depend.dot')
Gtmp = nx.nx_pydot.from_pydot(Gtmp)
G = nx.DiGraph(Gtmp)


needed = ['Cshmgen', 'Csharpminor', 'SimplExpr', 'SimplLocals', 'Frontend', 'PrintClight', 'PrintCsharpminor', 'Cminor', 'Cexec']

current_set = set(needed)
queue = needed

while queue != []:
  curr = queue.pop(0)
  for out in G.out_edges(curr):
    if out[1] not in current_set:
      current_set.add(out[1])
      queue.append(out[1])

result = list(current_set)

result.sort()

rootOrg = os.getcwd()
rootDst = os.path.join(rootOrg, "customLib")

moves = []

for i in result:
  mlname = "{}.ml".format(i)
  mliname = "{}.mli".format(i)
  ml_l = glob.glob(rootOrg + "/**/{}.ml".format(i))
  mli_l = glob.glob(rootOrg + "/**/{}.mli".format(i))
  if len(ml_l) >= 1:
    if len(ml_l) > 1:
      ml_l = [i for i in ml_l if "x86" in i]
      if len(ml_l) > 1:
        ml_l = [i for i in ml_l if "x86_64" in i]
    ml = ml_l[0]
    moves.append((mlname, ml))
  if len(mli_l) >= 1:
    if len(mli_l) > 1:
      mli_l = [i for i in mli_l if "x86" in i]
      if len(ml_l) > 1:
        mli_l = [i for i in mli_l if "x86_64" in i]
    mli = mli_l[0]
    moves.append((mliname, mli))


scriptLines = []
for mv in moves:
  org = mv[1]
  dst = os.path.join(rootDst, mv[0])
  cmd = "cp {} {}".format(org, dst)
  scriptLines.append(cmd)

script = "\n".join(scriptLines)
with open("moveScript.sh", "w") as f:
  f.write(script)
  f.close()
  