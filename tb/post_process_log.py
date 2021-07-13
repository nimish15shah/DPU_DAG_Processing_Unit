
import os

os.system("grep -in Offending log/run_log | grep -vi isunknown")

os.system("grep -in golden log/run_log")
os.system("grep -n Test log/run_log")
