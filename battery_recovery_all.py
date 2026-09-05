import math
import subprocess
import json
import time
import math
import csv
import random

FILENAME = "CREATE_A_FILE.txt"
F_SIZE = 24
SCRIPT="decoder.sage"
TIMEOUT = 60*4 # currently no time out needed - I know the algorithm will terminate


#n = [25,50,100,150,200,250]
#n = 25
# fract. noise tolerated?
#fracts = [0.55, 0.65, 0.75, 0.80]

def write_res(list_st):
    with open(FILENAME, "a",newline='') as fileobj:
        csv_writer = csv.writer(fileobj)
        csv_writer.writerow(list_st)

def run_tests_with_exact_distr(c,n,ell,agreement):
    bad_cases = 0
    fail_cases = 0
    k = 1
    t = 1
    hns = int(n / agreement) 
    # try for some exact distr. here 
    for _ in range(5):
        num_left = n
        if hns == 1:
            st = 1
        else:
            st = random.randrange(1,hns)
        lk = 0
        if st != hns:
            lk = random.randrange(0,hns-st)
        in_distr = [agreement] * st
        num_left -= (agreement*st)
        for _ in range(lk):
            nib = random.randrange(ell, agreement)
            num_left -= nib 
            in_distr.append(nib)    
        in_distr.append(num_left)     
        #print("TESTS WITH IN BETWEEN NUMBERS OF POINTS")
        #print("AGREEMENT PARAM: {}".format(agreement))
        #print("DISTR: {}".format(in_distr))         
        try:
            to_report = subprocess.check_output(["sage", SCRIPT, str(c), str(n), str(ell), str(F_SIZE), str(agreement), "--exact_distr", str(in_distr)],timeout=TIMEOUT)
            to_r_json = json.loads(to_report) 
            w_t_csv = [c, n, ell, agreement, k, t] + to_r_json
            if not w_t_csv[7]:
                bad_cases += 1
                print("FAIL STOPPING!!!")
                import pdb; pdb.set_trace()
            # report first
            write_res(w_t_csv) 
        except subprocess.TimeoutExpired:
            print("HIT A TIMEOUT")
            fail_cases += 1
            import pdb; pdb.set_trace()
            w_t_csv = [c,n,ell,agreement,k,t,"TIMEOUT"]
            write_res(w_t_csv)        
        except subprocess.CalledProcessError as e:
            print("Unexpected error attempting to run list decoding alg.")
            print(e)
            import pdb; pdb.set_trace()
            fail_cases += 1
            w_t_csv = [c,n,ell,agreement,k,t,"FAILED"]
            write_res(w_t_csv)
    return bad_cases, fail_cases 
    
        
    
# goes through all distr I guess. 
def run_tests_with_distr(c,n,ell,agreement):
    global RUNS_PER_DISTR
    bad_cases = 0
    fail_cases = 0
    k = 1
    t = 1
    
    for j in range(5):
        for _ in range(RUNS_PER_DISTR[j]):
            # run the code and try to slack
            try:
                to_report = subprocess.check_output(["sage", SCRIPT, str(c), str(n), str(ell), str(F_SIZE), str(agreement), "--distr", str(j)],timeout=TIMEOUT)
                to_r_json = json.loads(to_report) 
                w_t_csv = [c, n, ell, agreement, k, t] + to_r_json
                if not w_t_csv[7]:
                    print("FAIL STOPPING!!!")
                    import pdb; pdb.set_trace()
                    bad_cases += 1
                # report first
                write_res(w_t_csv) 
        # first, check if the check was successful or if it failed
        # if it *maybe* could have passed with higher parameters, do some more tests
            except subprocess.TimeoutExpired:
                print("HIT A TIMEOUT")
                import pdb; pdb.set_trace()
                fail_cases += 1
                w_t_csv = [c,n,ell,agreement,k,t,"TIMEOUT"]
                write_res(w_t_csv)        
            except subprocess.CalledProcessError as e:
                print("Unexpected error attempting to run list decoding alg.")
                print(e)
                import pdb; pdb.set_trace()
                fail_cases += 1
                w_t_csv = [c,n,ell,agreement,k,t,"FAILED"]
                write_res(w_t_csv)
    return bad_cases, fail_cases 
    
        

if __name__ == "__main__":
    NORM_BAD_CASES = 0
    FAIL_CASES = 0
    RUNS_PER_DISTR = [10,10,10,10]
    #RUNS_PER_DISTR = [25, 50, 250, 200]
    #RUNS_PER_DISTR = [25,50,100,100,50]
    write_res(["C", "N", "K", "T", "MULTIPLICITY", "MAX DEGREE/SHIFT", "TIME", "COMPLETELY CORRECT", "NUM SOLNS FOUND", "STALKERS PTS", "NUM RANDOM ERRORS"])
    #cs = [2,4,10,12]
    #cs = [3,5,6,8,15]
    cs = [2,7,9,11,13]
    n_base = 100
    #ells = [2,10,16,28]
    #ells = [6,13,25]
    ells = [3,5,7,28]
    for ell in ells:
        for c in cs: 
            for n_add in range(c+1): 
                n = n_base + n_add
                agreement = int(math.ceil((1.0/(c+1))*(c*ell + n)))+1 
                out_bad, out_fail = run_tests_with_distr(c,n,ell,agreement)
                #out_bad2, out_fail2 = run_tests_with_exact_distr(c,n,ell,agreement)
                NORM_BAD_CASES += out_bad
                #NORM_BAD_CASES += out_bad2
                FAIL_CASES += out_fail
                #FAIL_CASES += out_fail2
    print("Number of incorrect results: {}\nNumber of failures to terminate properly: {}".format(NORM_BAD_CASES, FAIL_CASES))
