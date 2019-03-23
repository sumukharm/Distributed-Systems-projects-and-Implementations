#once check all codes before running this
import os
from datetime import datetime, timedelta
import subprocess

runs = 5 #min 2
timeout = 1
for i in range(5, 21, 5):
	os.system("python -m da main.da {} {} {} {} {} > log_file_{}_{}_{}_{}_{}".format(i,runs,0,0,timeout,i,runs,0,0,datetime.today().strftime("%Y-%m-%d-%H-%M-%S")))
	print("python3.6 -m da main.da {} {} {} {} {} > log_file_{}_{}_{}_{}_{}".format(i,runs,0,0,timeout,i,runs,0,0,datetime.today().strftime("%Y:%m:%d:%H:%M:%S")))