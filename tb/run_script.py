
import os
import subprocess

partition_datasets= [\
   'ad', \
   'jester', \
   'msweb', \
   'mnist', \
   'msnbc', \
   'tretail', \
   'bbc', \
   'book', \
   'cr52', \
   'cwebkb', \
   'c20ng', \

#    'nltcs', \
#    'mnist', \
#    'msnbc', \
#    'msweb', \
#    'tretail', \
#    'bnetflix', \
#    'ad', \
#    'jester', \
#    'bbc', \
#    'book', \
#    'cr52', \
#    'cwebkb', \
#    'c20ng', \
#    'kdd', \
#    'baudio', \
#    'pumsb_star', \
  ]

partition_datasets =[
  'HB_orani678',  
  # 'HB_bcsstk08',
  'HB_bcsstk21',
  'HB_orsreg_1',
  'Bai_rdb3200l',
  # 'HB_sherman2',
  # 'HB_lshp3025',
  # 'Bai_dw8192',
  # 'Bai_dw4096',
  # 'Bai_cryg10000',
  # 'Bai_rdb5000',
  ]



def run(log_path, name_ls):
  run_log= open(log_path, 'a+')
  print("Start", file= run_log, flush=True)

  for name in name_ls:
    print(name)
    # cmd= f"make run NET={name} | grep clk_cycles"
    cmd= f"make run_w_script NET={name}" 
    print(cmd)
    
    output= subprocess.check_output(cmd, shell=True)
    output = str(output)
    output = output[:-3]
    output= output[output.find('clk_cycles'):]
    output= output[: output.find('\\n')]
    print(output)
    print(f"{name},{output}", file= run_log, flush= True)

def sv_compile(th):
  cmd= f"sed -i '31s/.*/  parameter N_PE                = {th};/' ../src/common.sv"
  os.system(cmd)

  cmd= "make compile"
  os.system(cmd)

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

def main():
  # 5000-25000
  # name_ls= ['HB/west0479', 'HB/lns_511', 'HB/lshp_577', 'HB/sherman4', 'HB/west1505', 'HB/fs_541_3', 'HB/west2021', 'Pothen/mesh2e1', 'HB/662_bus', 'Bai/bfwa398', 'Bai/mhd3200b', 'HB/west0655', 'Bai/qh882', 'HB/gre_343', 'Bai/qh1484', 'HB/gre_512', 'MathWorks/Sieber', 'Bai/dw256A', 'HB/fs_541_4', 'HB/bcsstk19', 'HB/west0381', 'Bai/bfwb398', 'Bai/dw256B', 'Bai/bfwa782', 'HB/mahindas', 'Bai/rw496', 'HB/gre_216a', 'Bai/olm5000', 'HB/fs_541_2', 'HB/bp_200', 'FIDAP/ex1', 'Pothen/mesh3em5', 'HB/steam1', 'HB/lshp_406', 'HB/bp_1200', 'Bai/bfwb782', 'HB/bp_1600', 'HB/bcsstm25', 'HB/lund_a', 'Bai/bwm2000', 'Pothen/mesh2em5', 'HB/bp_600', 'Bai/rdb450l', 'Bai/rdb200l', 'HB/shl_400', 'HB/dwt_361', 'HB/bp_1000', 'Bai/dwa512', 'HB/bp_400', 'HB/nos6', 'HB/nnc666', 'HB/685_bus', 'HB/young3c', 'HB/lshp_265', 'HB/plat362', 'Bai/rdb450', 'Bai/dwb512', 'HB/pores_3', 'Pothen/sphere3', 'HB/jagmesh5', 'Bai/tols4000', 'Norris/lung1', 'HB/lnsp_511', 'MathWorks/Pd', 'HB/fs_541_1', 'HB/1138_bus', 'HB/bp_1400', 'HB/lund_b', 'Bai/rdb200', 'HB/plskz362', 'Pothen/mesh3e1', 'HB/bp_800', 'HB/dwt_503', 'Oberwolfach/t3dl_e', 'HB/gre_185', 'HB/bcsstk04']

  # 5000-10000
  name_ls= ['Bai/dwb512', 'Pothen/mesh3e1', 'Bai/dwa512', 'Pothen/mesh2em5', 'HB/west1505', 'HB/fs_541_2', 'HB/dwt_361', 'Pothen/sphere3', 'HB/west0381', 'HB/bp_400', 'HB/gre_185', 'HB/685_bus', 'HB/west2021', 'HB/lshp_406', 'Bai/rw496', 'HB/lshp_265', 'HB/bp_200', 'Norris/lung1', 'FIDAP/ex1', 'HB/west0655', 'HB/shl_400', 'HB/fs_541_1', 'Bai/rdb200l', 'Bai/bfwa398', 'HB/dwt_503', 'HB/lund_a', 'HB/lund_b', 'Bai/bfwb398', 'HB/fs_541_4', 'HB/bcsstk04', 'HB/pores_3', 'HB/gre_343', 'Bai/dw256B', 'HB/1138_bus', 'Bai/rdb200', 'HB/plskz362', 'Bai/dw256A', 'Bai/qh1484', 'Bai/tols4000', 'Bai/qh882', 'HB/gre_216a', 'Pothen/mesh3em5', 'HB/662_bus', 'Pothen/mesh2e1', 'HB/steam1', 'Bai/bwm2000', 'MathWorks/Pd', 'HB/west0479']

  name_ls= ['Norris/lung1']
  # size: 5000 to 25000 size
  name_ls= ['Pothen/mesh3e1', 'HB/plskz362', 'Bai/dwa512', 'HB/bp_1200', 'Pothen/sphere3', 'HB/bcsstm25', 'HB/gre_216a', 'HB/fs_541_4', 'HB/dwt_503', 'Bai/bfwb398', 'HB/bp_200', 'HB/west2021', 'HB/bp_800', 'Bai/dwb512', 'Bai/olm5000', 'HB/gre_185', 'Bai/bfwa398', 'Pothen/mesh3em5', 'Bai/dw256A', 'HB/lnsp_511', 'Bai/rw496', 'HB/lshp_406', 'HB/bp_600', 'Pothen/mesh2e1', 'Norris/lung1', 'HB/685_bus', 'Bai/dw256B', 'HB/bcsstk04', 'Bai/rdb200', 'HB/1138_bus', 'HB/bp_1400', 'HB/west0655', 'Oberwolfach/t3dl_e', 'HB/nos6', 'HB/fs_541_2', 'Bai/bfwb782', 'HB/plat362', 'HB/662_bus', 'HB/lshp_265', 'HB/nnc666', 'HB/bcsstk19', 'Bai/tols4000', 'Pothen/mesh2em5', 'HB/lshp_577', 'Bai/rdb200l', 'Bai/bwm2000', 'HB/shl_400', 'HB/bp_1000', 'HB/west1505', 'HB/jagmesh5', 'MathWorks/Sieber', 'MathWorks/Pd', 'HB/bp_1600', 'Bai/mhd3200b', 'HB/lns_511', 'HB/west0479', 'Bai/rdb450l', 'HB/pores_3', 'HB/sherman4', 'HB/gre_343', 'HB/mahindas', 'HB/dwt_361', 'HB/lund_a', 'Bai/bfwa782', 'HB/steam1', 'FIDAP/ex1', 'HB/fs_541_3', 'HB/gre_512', 'HB/young3c', 'HB/west0381', 'HB/bp_400', 'Bai/rdb450', 'Bai/qh882', 'Bai/qh1484', 'HB/lund_b', 'HB/fs_541_1']

  # 25000 to 50000
  name_ls= [ 'HB/jagmesh7', 'HB/jagmesh3', 'HB/fs_760_1', 'HB/can_445', 'HB/nos5', 'Bai/cdde3', 'Oberwolfach/rail_1357', 'HB/mcfe', 'HB/fs_760_3', 'Bai/pde900', 'HB/gr_30_30', 'Bai/mhda416', 'HB/fs_760_2', 'Bai/rdb800l', 'Oberwolfach/spiral', 'HB/bcsstk07', 'FIDAP/ex2', 'HB/bcsstk06', 'HB/bcsstm07', 'HB/jagmesh8', 'Bai/cdde1', 'Bai/cdde5', 'HB/sherman1', 'HB/jagmesh4', 'Bai/cdde4', 'HB/can_838', 'HB/jagmesh1', 'HB/steam2', 'FIDAP/ex32', 'HB/plsk1919', 'HB/lshp_778', 'HB/lshp1009', 'Bai/cdde6', 'HB/jagmesh2', 'Bai/cdde2', 'HB/hor_131', 'FIDAP/ex22', 'Bai/mhd4800b', 'HB/jagmesh6', 'HB/bcsstk10', 'HB/bcsstm10', 'HB/pores_2']


  # spn
  # name_ls = [\
    # 'ad', \
    # 'baudio', \
    # 'bbc', \
    # 'bnetflix', \
    # 'book', \
    # 'c20ng', \
    # 'cr52', \
    # 'cwebkb', \
    # 'jester', \
    # 'kdd', \
    # 'mnist', \
    # 'msnbc', \
    # 'msweb', \
    # 'nltcs', \
    # 'pumsb_star', \
    # 'tretail', \
  # ]

  th_ls= [2,4,8,16,32,64]
  for th in th_ls:
    name_ls = replace_slash(name_ls)
    log_path= f"run_log_sparse_tr_{th}_8192_8192_large_stream_mem"
    sv_compile(th)
    run(log_path, name_ls)

if __name__ == "__main__":
  main()

