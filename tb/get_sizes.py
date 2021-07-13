
import csv

def replace_slash(name_ls):
  group_names= ["Bai", 
      "Bindel",
      "HB",
      "Norris",
      "GHS_indef",
      "GHS_psdef",
      "FIDAP",
      "Boeing",
      "Oberwolfach",
      "Pothen",
      "MathWorks",
      "Nasa",
      "Pothen"
      ]
  
  new_name_ls= []
  for name in name_ls:
    for g in group_names:
      name= name.replace(g+'/', g+'_', 1)
    
    new_name_ls.append(name)

  return new_name_ls

def replace_underscore(name_ls):
  group_names= ["Bai", 
      "Bindel",
      "HB",
      "Norris",
      "GHS_indef",
      "GHS_psdef",
      "FIDAP",
      "Boeing",
      "Oberwolfach",
      "Pothen",
      "MathWorks",
      "Nasa",
      "Pothen"
      ]
  
  new_name_ls= []
  for name in name_ls:
    for g in group_names:
      name= name.replace(g+'_', g+'/', 1)
    
    new_name_ls.append(name)

  return new_name_ls

def get_matrix_sizes(name_format= 'under_score'):
  assert name_format in ['under_score', 'slash']

  fname= '/users/micas/nshah/Downloads/PhD/Academic/Bayesian_Networks_project/Hardware_Implementation/Auto_RTL_Generation/HW_files/scripts/graph_analysis_3/src/openmp/sparse_tr_solve_mat_sizes'
  with open(fname, 'r') as fp:
    data = csv.reader(fp, delimiter=',')
    data= list(data)

    name_idx= 0
    col_idx= 4
    compute_idx= 6

    compute_d= {}
    cols_d= {}
    for d in data:
      if len(d) == 1:
        assert d[0] == 'Start'
        continue
      name= d[name_idx].strip()
      cols= int(d[col_idx])
      compute= int(d[compute_idx])

      if name_format == 'slash':
        name= replace_underscore([name])[0]
      
      compute_d[name] = compute
      cols_d[name]= cols
  
  return compute_d

def get_psdd_sizes():
  fname= '/users/micas/nshah/Downloads/PhD/Academic/Bayesian_Networks_project/Hardware_Implementation/Auto_RTL_Generation/HW_files/scripts/graph_analysis_3/src/openmp/psdd_sizes'
  with open(fname, 'r') as fp:
    data = csv.reader(fp, delimiter=',')
    data= list(data)
    
    # first line is title
    data = data[1:]

    name_idx= 0
    leaves_idx= 3
    compute_idx= 4

    compute_d= {}
    for d in data:
      if len(d) == 1:
        assert d[0] == 'Start'
        continue
      name= d[name_idx].strip()
      compute= int(d[compute_idx])

      compute_d[name] = compute
  
  return compute_d

