#!/usr/bin/env sage
import argparse
import json
import math
import pickle
import time

from random import randint,shuffle,choice

from sage.all import GF, Integer, Matrix, PolynomialRing, prod, Parallelism, Subsets
from sage.combinat import combination

import logging
logger = logging.getLogger(__name__)


# --- FROM INSTANCE GENERATION FILE ------------

def convert_poly_to_set(poly_1): 
    pts = []
    for factor,deg in poly_1.factor():
        if deg == 1:
            pts.append(-factor.constant_coefficient())
    return set(pts)

def gen_unique_elements(field, n):
    evaluation_points = []
    for i in range(n):
        elt = field.random_element()
        while elt in evaluation_points:
            elt = field.random_element()
        evaluation_points.append(elt)
    return evaluation_points

def random_polynomial(pR, degree):
    z = pR.gens()[0]
    return pR.random_element(degree=degree)
    # TODO: SWITCH BACK
    #return pR.random_element(degree=degree - 1) + z ^ degree

def rand_poly_less_or_equal(pR, degree):
    return pR.random_element(degree=(0,degree))

def gen_mult_inst(field, pR, c, n, ell):
    # temporary, just want to see if I can get an example satisfying Harry's requirements 
    # one solution with one additional point, the other with one less 
    err = 0
    if n % 2 == 0:
        small_ag = int((n-2)/2)
        large_ag = small_ag + 1
        err = 1
    else:
        small_ag = int((n-1)/2)
        large_ag = n - small_ag
    
    # sample the og with matching degree
    fs = [random_polynomial(pR, ell) for i in range(c)]

    # sample coords
    eval_points = gen_unique_elements(field, n)
    # order is [to og | to second | to err]
    err_poly2 = pR(1)
    z = pR.gens()[0]
    for i in range(large_ag):
        err_poly2 *= (z-eval_points[i])
    err_poly1 = pR(1)
    for i in range(small_ag):
        err_poly1 *= (z-eval_points[large_ag+i])
    if err != 0:
        err_poly2 *= (z-eval_points[-1])
        err_poly1 *= (z-eval_points[-1])
    # Goal is to find 
    # a,b,c constants s.t 
    # (a*z+b)err_poly1 + c*err_poly2 is one degree shorter than err_poly1 
    # a=c can be uniformly chosen
    # b chosen to knock down degree
    a = field.random_element()
    # check 
    res = a*z*err_poly1 - a*err_poly2 
    b = res.leading_coefficient() 
    gis = []
    for i in range(c):
        # first, set the first coeff. to be equal to the leading coefficient of p_i
        dk = fs[i].leading_coefficient()
        # to calculate others,
        first_poly = (a*z-b)*err_poly1*fs[i]
        tmp_c = (first_poly - a*err_poly2*(dk*z^(ell-1))).leading_coefficient()
        dkl = tmp_c*a.inverse() 
        g_i = dk*z^(ell) + dkl*z^(ell-1) + random_polynomial(pR,ell-3)  
        gis.append(g_i)
    # create the codeword from this 
    cw = []
    x_coords = [pR(1),pR(1),pR(1)]
    rand_coords = []
    for i in range(large_ag):
        # this is the f's 
        y_coords = [f(eval_points[i]) for f in fs]
        x_coords[0] *= (z - eval_points[i])
        cw.append([eval_points[i],y_coords])
    for i in range(small_ag):
        # this is the f's 
        y_coords = [gi(eval_points[large_ag+i]) for gi in gis]
        x_coords[1] *= (z-eval_points[large_ag+i])
        cw.append([eval_points[large_ag+i],y_coords])
    if err != 0:
        # one more point to add 
        y_coords = [field.random_element() for i in range(c)] 
        x_coords[-1] *= (z-eval_points[-1])
        rand_coords.append(eval_points[-1])
        cw.append([eval_points[-1],y_coords])
    return [int(large_ag),int(small_ag)], [fs,gis], cw, x_coords, rand_coords        

    """
    # calculate error polynomials, do the easiest assumption (first half

    # simple test for what happens when the target vector is a multiple of one injected by an adversary
    ps = []
    for i in range(c):
        ps.append(random_polynomial(pR, ell))
    scal_p = field.random_element()
    gs = []
    for p in ps:
        gs.append(scal_p*p)
    eval_points = gen_unique_elements(field, n)
    num_each = int(math.floor(n / 2))
    list_stalkers = [num_each,num_each]
    codeword = []
    z = pR.gens()[0]
    x_coords = [pR(1),pR(1)]
    rand_coords = eval_points[2*num_each:]

    for j in range(2*num_each):
        if j % 2 == 0:
            # evaluate first set 
            pts = [ps[k](eval_points[j]) for k in range(c)]
            x_coords[0] *= (z - eval_points[j])
            codeword.append([eval_points[j],pts])
        else:
            pts = [gs[k](eval_points[j]) for k in range(c)]
            x_coords[1] *= (z - eval_points[j])
            codeword.append([eval_points[j],pts])
     
    return list_stalkers, [ps,gs], codeword, x_coords, rand_coords        
    """

def gen_cross_inst(field, pR, c, n, ell, num_ag):
    num_coll = 1
    # most simple instance description: 
    # [num_ag, num_ag] list stalkers 
    # num of other rand pts - n-(num_ag*2)+1 ** because of overlap 
    xtra_pts = ell+1 - num_coll
    a_s = []
    b_s = []
    for j in range(xtra_pts):
        a = [field.random_element() for i in range(c)]
        b = [field.random_element() for i in range(c)]
        a_s.append(a)
        b_s.append(b) 
    list_stalkers = []
    all_same = []
    for i in range(num_coll):
        same_point = [field.random_element() for j in range(c)]
        all_same.append(same_point)
    # back fill the rest of the points evenly 
    eval_points = gen_unique_elements(field, n)
    # the actual set of polys
    set1 = []
    set2 = []
    for i in range(c):
        eval_itr = 0
        s_f = [(eval_points[j], all_same[j][i]) for j in range(num_coll)]
        eval_itr += num_coll
        s_fa = s_f.copy()
        for j in range(xtra_pts):
            s_fa.append((eval_points[eval_itr+j] ,a_s[j][i]))
        eval_itr += xtra_pts
        s_fb = s_f.copy()
        for j in range(xtra_pts):
            s_fb.append((eval_points[eval_itr+j], b_s[j][i]))
        
        fa = pR.lagrange_polynomial(s_fa) 
        fb = pR.lagrange_polynomial(s_fb)
        set1.append(fa)
        set2.append(fb)
    # eval_pts:
    # [  coll_pts  ] [ f_1 ] [ f_2 ] [leftover f_1] [leftover f_2 ]  [rand_pts]
    up_to_ag = num_ag - (ell + 1)
    num_rand = n - (2*num_ag - num_coll)
    list_stalkers = [num_ag,num_ag]
    codeword = []
    z = pR.gens()[0]
    x_coords = [pR(1),pR(1)]
    for i in range(num_coll):
        codeword.append([eval_points[i],all_same[i]])
        x_coords[0] *= (z - eval_points[i])
        x_coords[1] *= (z - eval_points[i])
    eval_itr = num_coll
    for j in range(ell+1 - num_coll):
        pts = [set1[k](eval_points[eval_itr+j]) for k in range(c)]
        codeword.append([eval_points[eval_itr+j], pts])
        x_coords[0] *= (z - eval_points[eval_itr+j])
    eval_itr += (ell+1 - num_coll)
    for j in range(ell+1 - num_coll):
        pts = [set2[k](eval_points[eval_itr+j]) for k in range(c)]
        codeword.append([eval_points[eval_itr+j], pts]) 
        x_coords[1] *= (z - eval_points[eval_itr+j])
    eval_itr += (ell+1 - num_coll)
    for j in range(up_to_ag):
        pts = [set1[k](eval_points[eval_itr+j]) for k in range(c)]
        codeword.append([eval_points[eval_itr+j], pts]) 
        x_coords[0] *= (z - eval_points[eval_itr+j])
    eval_itr += up_to_ag
    for j in range(up_to_ag):
        pts = [set2[k](eval_points[eval_itr+j]) for k in range(c)]
        codeword.append([eval_points[eval_itr+j], pts]) 
        x_coords[1] *= (z - eval_points[eval_itr+j])
    eval_itr += up_to_ag
    # now we just have leftover values 
    x_coords.append(pR(1))
    for j in range(num_rand):
        # random values please 
        pts = [field.random_element() for i in range(c)]
        codeword.append([eval_points[eval_itr+j], pts])       
        x_coords[-1] *= (z - eval_points[eval_itr+j])
    list_stalkers[0] = int(list_stalkers[0])
    list_stalkers[1] = int(list_stalkers[1])
    return list_stalkers, [set1,set2], codeword, x_coords, []
         
# ell - m x c matrix describing the exact degree of each entry  
# m - number of embedded "solution" polys
# c - number of poly. evals. in a point 
# i.e. (x, y_1, ..., y_c)
# n - number of total points 
def gen_inst_from_config(field, pR, m, c, n, ell,evals):
    num_rand = n - sum(evals)
    f_list = []
    for i in range(m):
        vec_f = []
        for j in range(c):
            vec_f.append(random_polynomial(pR, ell[i][j]))
        f_list.append(vec_f)       
    eval_points = gen_unique_elements(field, n)
    random_x_coords = []
    if num_rand != 0:
        random_x_coords = eval_points[-num_rand:]
    x_coords = []
    codeword = []
    i = 0
    z = pR.gens()[0]
    for k in range(m):
        x_coords.append(pR(1))
        for j in range(evals[k]):
            x_coords[-1] *= (z - eval_points[i])
            codeword.append(
                [eval_points[i], list(fi(eval_points[i]) for fi in f_list[k])]
            )
            i += 1
    x_coords.append(pR(1))
    for j in range(num_rand):
        x_coords[-1] *= (z - eval_points[i])
        codeword.append(
            [eval_points[i], list(field.random_element() for fi in range(c))]
        )
        i += 1
    #TODO you need to take into  account that a random entry might agree with an input
    return f_list, codeword, x_coords, random_x_coords

def poly_from_list(poly_l, F, z):
    return sum([F(poly_l[i])*(z**i) for i in range(len(poly_l))])

def gen_inst_from_file(F, pR, m, c, n, ell, opts):
    # will need to reconstruct polys. from input of coefficients 
    z = pR.gens()[0] 
    raw_fl = opts["raw"]["f_list"]
    f_list = []
    for list_polys in raw_fl:
        fs = []
        for poly in list_polys:
            f = poly_from_list(poly, F, z)  
            fs.append(f)
        f_list.append(fs)
    # x_coords list of polys 
    x_coords = []
    for xp in opts["raw"]["x_coords"]:
        x_coords.append(poly_from_list(xp, F, z))
    # need evals as well, wish is the more complicated list of points 
    cw = []
    for pt in opts["raw"]["points"]:
        x_c = F(pt[0])
        ys = []
        for y in pt[1]:
            ys.append(F(y))
        cw.append([x_c, ys])
    random_x_coords = []
    for coord in opts["raw"]["random_x_coords"]:    
        random_x_coords.append(F(coord))
    return f_list, cw, x_coords, random_x_coords     


def gen_special_inst(fname):
    opts = {}
    file_obj = open(fname, "r") 
    try: 
        opts = json.load(file_obj) 
    finally:
        file_obj.close() 
        
    size_f = opts["f_size"]
    F = GF(size_f) 
    pR = PolynomialRing(F, "z")

    m = len(opts["evals"]) # is the number of eval pts 
    num_rand = opts["rand"]
    n = sum(opts["evals"]) + num_rand
    c = opts["c"] # number of poly evals in a point   
    ell_mtx = opts["ells"] # is the degree information... this is actually 
    # a MTX, very precise
    ell = opts["max_ell"]
    # reverse engineer the agreement param 
    ag = int(math.ceil((c*(ell + 1) + n)/(c+1)))
    
    d_conf = {
        "c": c, 
        "n": n,
        "ell": ell,
        "agreement": ag,
        "_field": F,
        "_pR": pR
    }
    indics_to_recover = []
    for i in range(len(opts["evals"])):
        eval = opts["evals"][i]
        if eval >= ag:
            indics_to_recover.append(i)

    f_list = []
    cw = []
    x_coords = []
    random_x_coords = []
  
    if "raw" in opts:
        f_list, cw, x_coords, random_x_coords = gen_inst_from_file(F, pR, m, c, n, ell_mtx, opts) 
    else:
        f_list, cw, x_coords, random_x_coords = gen_inst_from_config(F, pR, m, c, n, ell_mtx, opts["evals"])
     
    eval_err = opts["evals"] + [num_rand]
    return d_conf, indics_to_recover, eval_err, f_list, cw, x_coords, random_x_coords

def convert_poly_to_list(poly):
    as_list = poly.list()
    for i in range(len(as_list)):
        as_list[i] = int(as_list[i])
    return as_list

def write_to_file(fname, cw, f_list, x_coords, random_coords, max_ell):
    ells = []
    rfl = [] 
    for fs in f_list:
        ell_f = []
        rf = []
        for f in fs:
            rf.append(convert_poly_to_list(f))
            ell_f.append(int(f.degree())) 
        rfl.append(rf)  
        ells.append(ell_f)     
    all_evals = []
    rxc = []
    for x_list in x_coords:
        rxc.append(convert_poly_to_list(x_list))
        all_evals.append(int(x_list.degree()))
    save_obj = {
        "f_size": int(cw[0][0].base_ring().order()), 
        "c": len(f_list[0]),
        "evals": all_evals[:-1],
        "rand": all_evals[-1],
        "ells": ells,
        "max_ell": max_ell,
    }
    rrc = []
    for elt in random_coords:
        rrc.append(int(elt))
    rcw = []
    for pt in cw:
        rx = int(pt[0])
        rys = []
        for y in pt[1]:
            rys.append(int(y)) 
        rcw.append([rx, rys])
    raw_obj = {
        "f_list": rfl,
        "points": rcw,
        "x_coords": rxc,
        "random_x_coords": rrc,
    }
    save_obj["raw"] = raw_obj
    # use json to write this to a file
    out_file = open(fname, "w") 
    try:
        json.dump(save_obj,out_file)
    finally: 
        out_file.close()
    
    
    

# modified output to include information that is good for debugging 
def gen_adversarial_instance(field, pR, ell=6, c=3, evals=[12, 12, 1]):
    m = len(evals) - 1  # number of polynomial sets
    n = sum(evals)
    #f_list = [[random_polynomial(pR, ell) for i in range(c)] for j in range(m)]
    #rand_poly_less_or_equal 
    f_list = [[rand_poly_less_or_equal(pR, ell) for i in range(c)] for j in range(m)]
    eval_points = gen_unique_elements(field, n)
    random_x_coords = []
    if evals[-1] != 0:
        random_x_coords = eval_points[-evals[-1]:]
    x_coords = []
    codeword = []
    i = 0
    z = pR.gens()[0]
    for k in range(m):
        x_coords.append(pR(1))
        for j in range(evals[k]):
            x_coords[-1] *= (z - eval_points[i])
            codeword.append(
                [eval_points[i], list(fi(eval_points[i]) for fi in f_list[k])]
            )
            i += 1
    x_coords.append(pR(1))
    for j in range(evals[-1]):
        x_coords[-1] *= (z - eval_points[i])
        codeword.append(
            [eval_points[i], list(field.random_element() for fi in range(c))]
        )
        i += 1
    return f_list, codeword, x_coords, random_x_coords



# --------------------------------------------------

# output U s.t. Matrix(bvs) = U * S
def calculate_mtx(soln_mtx, bvs, z, ell, pR):
    comb_l = []
    for bv in bvs:
        bv_tmp = copy(bv)
        bv_tmp[0] = bv_tmp[0]*z**ell
        vtr = is_in_sublatt(soln_mtx, bv_tmp)
        if vtr == "Not in lattice":
            logger.info("You have a vector in the basis that is not in S")        
        else:
            comb_l.append(is_in_sublatt(soln_mtx, bv_tmp))

    comb_M = Matrix(comb_l).change_ring(pR)
    comb_M_cp = []
    for j in range(comb_M.ncols()):
        comb_M_cp.append(compute_norm(comb_M.column(j)))
    return (comb_M, comb_M_cp)


def print_current_pt_distr(message, x_coords_list, search_pts, z, x_indics):
    print_pts = [0] * (len(x_coords_list)) 
    for j in range(len(message)):
        if x_indics[j] == 1:
            stalker_l = 0
            for i in range(len(x_coords_list)):
                if (z - message[j][0]).divides(x_coords_list[i]):
                    stalker_l = i
                    break
            print_pts[stalker_l] += 1

    search_pt_idxs = []
    for search_pt in search_pts:
        not_found = True
        for i in range(len(x_coords_list)):
            if (z - search_pt).divides(x_coords_list[i]):
                not_found = False
                search_pt_idxs.append(i)
        if not_found:
            search_pt_idxs.append(-1)  
    for i in range(len(x_coords_list)): 
        amt = print_pts[i]
        logger.info("{} polynomial has {} pts".format(i, amt))
    lpr = []
    for i in range(len(x_coords_list)):
        amt = search_pt_idxs.count(i)
        lpr.append(amt)
        logger.info("{} points from polynomials {}".format(amt, i))
    return lpr 
    #for search_idx in search_pt_idxs:
    #    logger.info("A point from the {} polynomial is in the list of search points".format(search_idx))

def comb_test(mtx, pi, N, ell, z):
    global valid_polys, x_coords_list
    err = (N / x_coords_list[pi]) 
    tv = make_sol_vector(valid_polys[pi], err)
    tv[0] = tv[0] * z**ell
    return test_comb(mtx, tv)  

def identify_poly_found(solution_polys, sol_found):
    sol_idx = -1
    for i in range(len(solution_polys)):
        found_sol = True 
        # assume everything is the same size (it SHOULD be)
        if len(sol_found) != len(solution_polys[i]):
            raise Exception("Something really wrong here, probably with loading and writing instances to files")
        for j in range(len(solution_polys[i])): 
            if sol_found[j] != solution_polys[i][j]:
                found_sol = False
                break
        if found_sol:
            sol_idx = i
            break
    logger.info("Found polynomial solution corresponding to {}".format(sol_idx)) 
    return sol_idx

def scale_by(row, elt):
    scaled_row = []
    for row_val in row:
        scaled_row.append(row_val * elt)
    return scaled_row


def add_vectors(row1, row2):
    res = []
    for i in range(len(row1)):
        res.append(row1[i] + row2[i])
    return res

def poly_lin_comb(vs, scalars):
    if type(vs) == list:
        if len(scalars) != len(vs):
            return []
        out = scale_by(vs[0],scalars[0])
        for i in range(1, len(scalars)):
            out = add_vectors(out,scale_by(vs[i],scalars[i]))
    else: 
        # assume it is a matrix 
        out = list(scalars*vs) # maybe this is right?
    return out

def make_sol_vector(list_polys, errors):
    sol_vec = [1]
    for i in range(len(list_polys)):
        sol_vec.append(list_polys[i])
    return scale_by(sol_vec, errors)

# taken from here https://ask.sagemath.org/question/31754/add-a-row-column-to-a-matrix/
# and tweaked
# inserts the row last 
def insert_row(M, row):
    return matrix(M.rows()+[row])

def test_comb(input_mtx, sol_vector):
    input_comb = []
    if input_mtx.nrows() == input_mtx.ncols():
        inv_mtx = input_mtx.transpose().inverse()
        return inv_mtx*vector(sol_vector)
    else:
        #raise Exception("Does not work currently with non-square matrices")
        input_mtx = insert_row(input_mtx, sol_vector)
        col_mtx = input_mtx.transpose()
        res = col_mtx.echelon_form()
        # this is not the complete form of this algorithm 
        # for that you need to check 
        return res

def is_in_sublatt(input_mtx, sol_vector):
    # look at the dual 
    d_matt = input_mtx*input_mtx.transpose()
    # you may need to lift to field of rational
    # functions to do this operation 
    d_matt.change_ring(d_matt.base_ring().fraction_field())
    d_matt = d_matt.inverse()
    d_matt = d_matt*input_mtx 
    out = d_matt * vector(sol_vector)
    # you probably have to flip everything here
    # for row vs. column.
 
    # this is bad but return a string if you're not in the 
    # sublattice 
    for entry in out: 
        if out.denominator() != 1:
            return "Not in lattice"
    return out 

def lagr_reconstruct(message, recon_set,pR): 
    precon_li = []
    n = len(message)
    if n == 0:
        return [] # TODO: check this is probably impossible anyway
    c = len(message[0][1])
    for pt in recon_set: 
        find_pt = 0
        n = len(message)
        for j in range(n):
            x_coord, y_coords = message[j]
            if x_coord == pt: 
                find_pt = j
                break 
        precon_li.append(message[find_pt])
    poly_recon_att = []
    for i in range(c): 
        xy_v = [(precon_li[j][0], precon_li[j][1][i]) for j in range(len(precon_li))]
        poly_recon_att.append(pR.lagrange_polynomial(xy_v))
    return poly_recon_att

def project_onto(matt1, matt2, pR):
    assert(matt1.ncols() == matt2.ncols())
    # not clear how this call to block matrix is inappropriate here 
    flatten = block_matrix([[matt1],[-matt2]])
    # find the kernel
    kerL = flatten.left_kernel()
    # find the independent rows 
    b_vs = []
    divide = matt1.nrows()
    for vs in kerL.basis():
        first_comp = vs[:divide]
        b_vs.append(first_comp*matt1)
    return Matrix(b_vs)

def calculate_intersect(latt1, latt2,pR):
    # L1 \cap L2 = (L1^* + L2^*)^* \cap span(L1) \cap span(L2)
    l1d = (latt1*latt1.transpose()).inverse()*latt1
    l2d = (latt2*latt2.transpose()).inverse()*latt2
    # add them, calculate the number of rows that are independent
    add = block_matrix([[l1d],[l2d]])
    # maybe just try to get independent rows?    
    # if this is not a polynomial matrix I will need to figure out what I need to do to make sure this technique still works 
    lcm_fact = add[0][0].denominator()
    for ri in range(add.nrows()):
        for ci in range(add.ncols()):
            lcm_fact = lcm(lcm_fact, add[ri][ci].denominator())
    add = lcm_fact * add
    mtxA = add.change_ring(pR).popov_form() 
    nrows = mtxA.nrows()
    for ri in range(nrows-1,-1,-1):
        if mtxA[ri].is_zero():
            mtxA = mtxA[:-1]    
    mtxA = (1/lcm_fact) * mtxA
    # get rid of 0 rows 
    
    mtxAd = (mtxA*mtxA.transpose()).inverse()*mtxA
    #project onto the span of the lattice because they are not full rank 
    r1 = project_onto(mtxAd,latt1,pR)
    r2 = project_onto(r1,latt2,pR)
    return r2     

#TODO: make this change mtx_A
def weight(mtx_A, shifts,z):
    ncols = mtx_A.ncols()
    for j in range(ncols):
        mtx_A.rescale_col(j, z**shifts[j])
    return mtx_A

#TODO: make this change mtx_B            
def unweight(mtx_B, unshifts, z, pR):
    ncols = mtx_B.ncols()
    #B = copy(mtx_B)
    mtx_B = mtx_B.change_ring(mtx_B.base_ring().fraction_field())
    for j in range(ncols):
        fact = 1/z**unshifts[j]
        #print(fact)
        mtx_B.rescale_col(j, fact) 
    mtx_B = mtx_B.change_ring(pR)
    return mtx_B

def compute_norm(elt):
    max_deg = 0
    for i in elt:
        if i.degree() > max_deg:
            max_deg = i.degree()
    return max_deg

def compute_deg_mtx(mtx): 
    deg_mat = Matrix(mtx.nrows(),mtx.ncols())
    for i in range(mtx.nrows()):
        for j in range(mtx.ncols()):
            deg_mat[i,j] = mtx[i][j].degree()
    return deg_mat

def find_sv_len(mtx):
    if mtx.nrows() == 0:
        return None
    sv_len = compute_norm(mtx[0])
    for i in range(mtx.nrows()-1):
        cur_len = compute_norm(mtx[i+1])
        if cur_len < sv_len:
            sv_len = cur_len
    return sv_len 

def compute_row_profile(A):
    row_profile = []
    for row in A.rows():
        row_profile.append(compute_norm(row))
    return row_profile

def all_equal(row): 
    i = row[0]
    for j in row:
        if i != j:
            return False
    return True

class LagrInterpol:
    def __init__(self, pR, z, zs, c):
        self._pR = pR
        self._z = z
        self._c = c
        self.L = prod((z - zi) for zi in zs)
        # just L and bary weights now 
        Ls = [pR(self.L / (z - zi)) for zi in zs]
        Linvs = [1 / Li for Li in Ls]
        self.w = [Li(zi) for Li, zi in zip(Linvs, zs)]
        self.x_coords = [1] * len(zs)
        self.zs = zs

    def get_N(self):
        return self.L

    def internal_remove(self, removal_update):
        ch_poly = self._pR(1)
        for i,val in enumerate(removal_update):
            # this is looking for the update
            if val != 1 and self.x_coords[i] == 1:
                ch_poly *= (self._z-self.zs[i])
                # do the update
                self.x_coords[i] = val
        # TOTAL update to L
        self.L = self._pR(self.L / ch_poly)
        # use this deletion to update some other positions (every single weight) 
        for i,val in enumerate(self.x_coords):
            if val == 1:
                x_coord = self.zs[i] #message[i][0]
                self.w[i] = ch_poly(x_coord) * self.w[i]
        return

    def internal_add(self, add_update):
        ch_poly = self._pR(1)
        update_pos = []
        for i,val in enumerate(add_update):
            # this is looking for the update
            if val == 1 and self.x_coords[i] != 1:
                ch_poly *= (self._z-self.zs[i])
                # do the update
                # FOR THIS ONE WAIT TO DO THE UPDATE? 
                update_pos.append(i)

        # TOTAL update to L
        self.L = self.L * ch_poly

        # use this deletion to update some other positions (every single weight) 
        for i,val in enumerate(self.x_coords):
            if val == 1:
                x_coord = self.zs[i] #message[i][0]
                self.w[i] = self.w[i] / ch_poly(x_coord)
        
        # this is bary weights
        for i in update_pos:
            Li = self.L / (self._z - self.zs[i])
            self.w[i] =  1/Li(self.zs[i])
            self.x_coords[i] = 1
        return 

    def calculate(self,ys):
        result_polys = []
        for i in range(self._c):
            amt_r = 0
            for j in range(len(self.x_coords)):
                if self.x_coords[j] == 1:
                    amt_r += ys[j][i]*self.w[j] / (self._z-self.zs[j]) 
            result_polys.append(self.L * amt_r) 
        return result_polys
   
    #give updated lagr.coeffs from removing points in removal_update
    def update(self,removal_update):
        self.internal_remove(removal_update)
        return
      
    # refresh and remove 
    def randr(self,update):
        # what are you adding back  / what are you removing                 
        self.internal_remove(update)
        self.internal_add(update)
        return     
 

def barycentric_interpolate(L, w, ys, locs):
    # this is so wrong holy crap how did anything I have work before now? 
    
    # update correctly     
    # to remove something, multiply all other bary weights by that value 
    ch_poly = pR(1)
    for i,val in enumerate(locs):
        if val != 1 and (z-message[i][0]).divides(L):
            ch_poly *= (z-message[i][0])
    # use this deletion to update some other positions (every single weight) 
    for i,val in enumerate(locs):
        if val == 1:
            x_coord = message[i][0]
            w[i] = ch_poly(x_coord) * w_i
                
    return sum(ind * yi * Li * wi for ind, Li, wi, yi in zip(locs, Ls, w, ys))


def lagrange_basis(z, zs, pR):
    L = prod((z - zi) for zi in zs)
    # just L and bary weights now 
    Ls = [pR(L / (z - zi)) for zi in zs]
    Linvs = [1 / Li for Li in Ls]
    w = [Li(zi) for Li, zi in zip(Linvs, zs)]
    return L, Ls, w


def is_unique(some_msg):
    x_coords = [x[0] for x in some_msg]
    # unique = True

    # for x_coord in x_coords:
    #    if x_coords.count(x_coord) != 1:
    #        unique = False
    return len(x_coords) == len(set(x_coords))


# dropping the unused pos. stuff
def transl_to_set(idx_set):
    c_list = [idx_set[0]]
    for i in range(len(idx_set) - 1):
        c_list.append(idx_set[i + 1] - idx_set[i] - 1)
    return c_list

# can only be called on a reduced mtx 
def identify_pivots(mtx):
    p_ids = []
    for i in range(mtx.nrows()):
        mg2 = compute_norm(mtx[i])
        for j in range(mtx.ncols()-1,-1,-1):
            if mtx[i][j].degree() == mg2:
                p_ids.append(j)
                break
    return set(p_ids)      

class CHDecoder:
    def __init__(self, pR, c, n, ell, agreement, multiplicity=1, shift=1):
        self._c = c
        self._n = n
        self._ell = ell
        self._agreement = agreement
        self._pR = pR
        self._z = pR.gens()[0]
        # check that parameters are appropriately set
        if multiplicity != 1 or shift != 1:
            raise ValueError(
                "Cannot currently handle multiplicity or shift higher than one!"
            )
        self._k = multiplicity
        self._t = shift
     

    def create_interpols(self, message, locs):
        f = []

        # this is likely to be slow for now 
        real_locs = []
        for loc in locs:
            if loc == 2:
                real_locs.append(0)
            else: 
                real_locs.append(loc)
        ######################
        for i in range(self._c):
            ys = [m[1][i] for m in message]
            fi = barycentric_interpolate(self.Ls, self.w, ys, real_locs)
            f.append(fi)
        return f

    def unweightdual(self, M, i, ell):
        # only doing this for the shift = 1
        # multiplicity = 1 case for now
        # I will change back later if necessary
        
        resp = []
        resp.append(self._pR(M[i][0] / self._z**ell))
        for j in range(0, self._c):
            resp.append(M[i][j+1])
        return resp

    def find_agreeing_pts(self, polys, message, all_points):
        agree_pts = set()
        for pt in all_points:
            find_pt = 0
            for j in range(self._n):
                x_coord, y_coords = message[j]
                if x_coord == pt:
                    find_pt = j
                    break
            x_coord, y_coords = message[find_pt] 
            matches_all = True
            for i in range(self._c):
                try:
                    if polys[i](x_coord) != y_coords[i]:
                        matches_all = False
                        break
                except: 
                    raise ValueError("Failed in finding agreeing points phase!")
            if matches_all:
                agree_pts.add(pt)
        return agree_pts

    def remove_pts(self, message, resp_polys, x_indics):
        for i in range(len(message)):
            if x_indics[i] == 2:
                x_indics[i] = 1

            x_coord, y_coords = message[i]
            matches_all = True
            for j in range(self._c):
                if resp_polys[j](x_coord) != y_coords[j]:
                    matches_all = False
                    break
            if matches_all:
                x_indics[i] = 0 
        # bb update your priors
        self.lagrInfo.randr(x_indics)   
        return x_indics

    # NOTE: does *not* modify the input matrix
    def shifted_popov(self, rect_mtx, shifts):
        # TODO: just use the shifted option in the library (but for now, recall that this is all the opposite)
        inp = copy(rect_mtx)
        M_D = weight(inp, shifts, self._z)
        # swap columns 
        #M_D = copy(M_D).with_swapped_columns(0,self._c)
        A = M_D.weak_popov_form()
        ### LOGGER INFO ############        
        piv_A = identify_pivots(A)
        A_rp = compute_row_profile(A)
        un_deg = sum(A_rp)
        # recover shifted profile using pivot idx by selecting shift_I from shift and updating A_rp appropriately 
        shift_I = []
        for j in piv_A:
            shift_I.append(shifts[j])
        # this *should* be a subtraction
        shifted_deg = []
        for i in range(A.nrows()):
            shifted_deg.append(A_rp[i] - shift_I[i])
        #logger.info("True shifted degree: {}, total: {}".format(shifted_deg, sum(shifted_deg)))
        ############################
        #A = copy(A).with_swapped_columns(0,self._c)
        A = unweight(A, shifts, self._z, self._pR)
        return A, sum(shifted_deg), un_deg, piv_A

    def create_full_soln_mtx(self, x_indics, message, shifts, t, k):
        global valid_polys
        N = self.lagrInfo.get_N()
        if t != 1 or k != 1:
            if sum(shifts[1:]) != 0:
                raise ValueError("Can't support shift higher than 0 if multiplicity and shift is higher than 1")
        higher_sm = (t != 1 or k != 1)
        # DEBUGGING INFO
        num_sols = len(valid_polys)
        mtx_l = []
        # what solutions have been found so far?
        ftto = 1
        for idx,val in enumerate(x_indics):
            if val != 1:
                ftto *= (self._z-message[idx][0])
        # you need to use x_indics insstead for this most likely 
        mtx_l = []
        for j in range(num_sols):
            if higher_sm:
                vj = self.make_solve2(valid_polys[j], N / (x_coords_list[j]*ftto), t, k) 
            else:
                vj = make_sol_vector(valid_polys[j], N / (x_coords_list[j]*ftto))
                # shift the rows correctly 
                for i in range(len(shifts)):
                    vj[i] = vj[i] * self._z**shifts[i]
            mtx_l.append(vj)
        return Matrix(mtx_l) 

    # HELPER FUNCTIONS 
    # valid_polys and x_coord_list should both be globals (don't @ me) 
    def calculate_unimod(self, shortB, x_indics, message, shifts, t, k):
        N = self.lagrInfo.get_N()
        if t != 1 or k != 1:
            if sum(shifts[1:]) != 0:
                raise ValueError("Can't support shift higher than 0 if multiplicity and shift is higher than 1")
        higher_sm = (t != 1 or k != 1)
        global valid_polys, x_coords_list
        # DEBUGGING INFO
        num_sols = len(valid_polys)
        mtx_l = []
        # what solutions have been found so far?
        ftto = 1
        for idx,val in enumerate(x_indics):
            if val != 1:
                ftto *= (self._z-message[idx][0])
        # you need to use x_indics insstead for this most likely 

        for j in range(num_sols):
            vj = make_sol_vector(valid_polys[j], N / x_coords_list[j])
            if higher_sm:
                vj = self.make_solve2(valid_polys[j], N / x_coords_list[j],t,k)
            else:
                vj = make_sol_vector(valid_polys[j], N / x_coords_list[j])
                
                # shift the rows correctly 
                for i in range(len(shifts)):
                    vj[i] = vj[i]*self._z**shifts[i]
            lin_comb = is_in_sublatt(shortB, vj)
            mtx_l.append(lin_comb)
        return mtx_l

    def make_solve2(self, list_polys, errors, t, k):
        #TODO populate S, xs, M_LIST
        global M_LIST

        # we construct the multi var basis for polynomials
        # (then invert it)
        v = []
        for j,mon in enumerate(M_LIST):
            v.append(mon(list_polys))
        error_amp = errors**k
        # add the error scalars
        return scale_by(v, error_amp)

    def test_dual_mult_shift(self, message, locs, shifts, t, k):
        #TODO populate S, M_LIST
        global S, xs
        M_LIST = []
        for i in range(t+1):
            M_LIST += S.monomials_of_degree(i)
        
        # port defn for transl_to_set fn 
        def transl_to_set(idx_set):
            c_list = [idx_set[0]]
            for i in range(len(idx_set)-1):
                c_list.append(idx_set[i+1]-idx_set[i]-1)
            return c_list
        # t - shift, k - multiplicity
        ys = [symb[1] for symb in message]
        lagr_polys = self.lagrInfo.calculate(ys)
        N = self.lagrInfo.get_N()
        poly_list = []
        # we construct the multi var basis for polynomials
        # (then invert it)
        all_idxs = [x for x in range(t+self._c)]
        comb_opt = combination.Combinations(all_idxs,self._c)
        dp = {"n": [1]}
        n_powers = S(N)
        for w in range(k):
            dp["n"].append(n_powers)
            n_powers *= S(N)
        for i in range(self._c):
            dp[i] = [1]
            y_powers = S(xs[i] - lagr_polys[i])
            for w in range(t):
                dp[i].append(y_powers)
                y_powers *= S(xs[i] - lagr_polys[i])
        for opt in comb_opt:
            c_list = transl_to_set(opt)
            nth_pow = max(k-sum(c_list),0)
            term = dp["n"][nth_pow]
            for i in range(self._c):
                term *= dp[i][c_list[i]]
            poly_list.append(term)
        # this is tough because I also have the shifts on each position :/ 
        # (meaning this calculation could be wrong) 
        def weighted_coefficient_vector(hh):
            d = binomial(t+self._c, self._c)
            v = [0]*d
            for j,mon in enumerate(M_LIST):
                t_d = mon.degree()
                vw = self._ell*t_d
                #vw = 0
                v[j] = hh.monomial_coefficient(mon)*self._z^(vw)
            return v
        
        M = Matrix([weighted_coefficient_vector(h) for h in poly_list])     
        # take the dual 
        M_dual = M.inverse().transpose()
        Md = (N**k)*(self._z**(self._ell*t))*M_dual
        Md = Md.change_ring(self._pR).weak_popov_form()
        Md = Md.change_ring(self._pR.fraction_field())
        def unweighted_coefficient_vector(hh):
            d = binomial(t+self._c, self._c)
            v = [0]*d
            for j,mon in enumerate(M_LIST):
                t_d = mon.degree()
                vw = self._ell*(t-t_d)
                #vw = 0
                v[j] = hh[j] / self._z^(vw)
            return v
        Md2 = Matrix([unweighted_coefficient_vector(h) for h in Md]).change_ring(self._pR)
        #global valid_polys, x_coords_list
        #out2 = self.make_solve2(valid_polys[0],x_coords_list[0],3,2)
        return Md2        

    def first_step(self, message, locs, shifts):
        N = self.lagrInfo.get_N()
        ys = [message[i][1] for i in range(len(message))]
        lagr_polys = self.lagrInfo.calculate(ys)
        M_D = Matrix(self._pR, self._c + 1)
        M_D[0, 0] = 1

        for i in range(self._c):
            M_D[0, i + 1] = lagr_polys[i]
            M_D[i + 1, i + 1] = N
        # shift up
        M_D = weight(M_D, shifts, self._z)
        A = M_D.weak_popov_form()
        ### LOGGER INFO ############        
        piv_A = identify_pivots(A)
        A_rp = compute_row_profile(A)
        logger.info("Unshifted row profile: {}, Unshifted total: {}\n Pivot idxs:\n{}".format(A_rp, sum(A_rp),piv_A))
        # recover shifted profile using pivot idx by selecting shift_I from shift and updating A_rp appropriately 
        shift_I = []
        for j in piv_A:
            shift_I.append(shifts[j])
        # this *should* be a subtraction
        shifted_deg = []
        for i in range(A.nrows()):
            shifted_deg.append(A_rp[i] - shift_I[i])
        #logger.info("True shifted degree: {}, total: {}".format(shifted_deg, sum(shifted_deg)))
        ############################

        # shift down
        A = unweight(A, shifts, self._z, self._pR)
        return A

    def construct_one_out(self, basis_vectors, amplify, err_vec):
        for_testing = copy(basis_vectors)
        n_rows = len(for_testing)
        for i in range(n_rows):
            for_testing[i][0] *= amplify
            add_identity_row = [0]*i + [1] + [0]*(n_rows-i-1)
            for_testing[i] = for_testing[i] + add_identity_row

        num_cols = len(for_testing[0])
        last_row = [err_vec*amplify] + (num_cols-1)*[0]
        for_testing.append(last_row)
        #check_vals = Matrix(for_testing).change_ring(self._pR).weak_popov_form()
        check_vals = Matrix(for_testing).change_ring(self._pR).weak_popov_form()
        
        return check_vals

    def sublatt_solve(self,bvs,weight_factor,err_term):
        vs_to_add = []
        mtx_out = self.construct_one_out(bvs, weight_factor, err_term)
        # hand back short rows 
        sv_len = find_sv_len(mtx_out)
        for itr in range(mtx_out.nrows()):
            if compute_norm(mtx_out[itr]) == sv_len and mtx_out[itr][0] == self._pR(0):    
                # add the final
                scal_combo = mtx_out[itr][-len(bvs):]
                vs_to_add.append(scal_combo)
        return vs_to_add

    def alt_sublatt_solve(self,bvs, weight_factor, err_term):
        ebvs = []
        for row in bvs:
            ebvs.append([row[0]])
        b_len = bvs.nrows()
        mtx_out = self.construct_one_out(ebvs, weight_factor, err_term)
        # hand back short rows
        keep_below = weight_factor.degree()
        vs_to_add = []
        for itr in range(mtx_out.nrows()):
            if compute_norm(mtx_out[itr]) < keep_below and mtx_out[itr][0] == self._pR(0):
                # add the final
                scal_combo = mtx_out[itr][-b_len:]
                vs_to_add.append(scal_combo)
        return vs_to_add        

    def add_shortest_vectors(self,mtx):
        shortest_len = find_sv_len(mtx)
        add_all_short_vecs = [0] * mtx.ncols()
        for itr in range(mtx.nrows()):
            itr_vec = mtx[itr]
            if compute_norm(itr_vec) == shortest_len:
                add_all_short_vecs = add_vectors(add_all_short_vecs, itr_vec)
        return list(add_all_short_vecs)

    def compute_err_profile(self, A, ub_on_sol):
        err_profile = {}
        A_sub = []
        all_short = []
        stash_keys = []
        
        for i in range(A.nrows()):
            if compute_norm(A[i]) > ub_on_sol:
                continue
            A_sub.append(A[i])
            all_short.append(i)
            afact = gcd(A[i][0], self.N) 
            if not afact in err_profile: 
                err_profile[afact] = set()
                stash_keys.append(afact)
            err_profile[afact].add(i)
        for key_val in stash_keys: 
            for other_key in stash_keys:
                if key_val != self._pR(1) and key_val != other_key:
                    new_key = gcd(key_val, other_key)
                    if not new_key in err_profile:
                        # merge sets 
                        new_set = err_profile[key_val].union(err_profile[other_key])
                        err_profile[new_key] = new_set    
                    elif new_key != self._pR(1):
                        err_profile[new_key] = err_profile[new_key].union(err_profile[other_key])
                        err_profile[new_key] = err_profile[new_key].union(err_profile[key_val]) 

        A_subm = Matrix(A_sub)
        if A_subm.nrows() == 0:
            logger.info("Went through err_compute_profile and found no short vectors")
            return err_profile
        gcd_all = gcd(self.N,A_subm[0][0])
        for i in range(A_subm.nrows()):
            gcd_all = gcd(gcd_all, A_subm[i][0])
        err_profile[gcd_all] = set(all_short)
        return err_profile 

    def check_sol_in_basis(self, A, ub_on_sol):
        global valid_polys
        for row in A:
            c_r = [row[i] for i in range(len(row))]
            if c_r[0] == self._pR(0):
                continue
            rpolys = c_r[1:]
            rpolys = [
                x / c_r[0]
                for x in rpolys
            ]
            if compute_norm(row) <= ub_on_sol:
                all_divides = True
                for i in range(self._c):
                    if not c_r[0].divides(c_r[i+1]):
                        all_divides = False
                        break
                if all_divides:
                    rpolys = [
                        self._pR(x)
                        for x in rpolys
                    ]
                    if compute_norm(rpolys) <= self._ell:
                        logger.info("Found solution in first reduction")
                        identify_poly_found(valid_polys, rpolys)
                        return rpolys
        return []

    def check_one_sol_out(self,A,ub_on_sol,message):
        A_sm = []
        for row in A:
            if compute_norm(row) <= ub_on_sol:
                A_sm.append(row)
        for row1 in A_sm:
            for row2 in A_sm:
                if row1 != row2:
                    err_col1 = gcd(self.N, row1[0])
                    err_col2 = gcd(self.N, row2[0])
                    if err_col1.divides(err_col2):
                        rf_1 = row1[1:]
                        rf_10 = self._pR(row1[0])
                        rf_1 = [x/rf_10 for x in rf_1]
                        rf_2 = row2[1:]
                        rf_20 = self._pR(row2[0])
                        rf_2 = [x/rf_20 for x in rf_2]
   
                        setOne = self.find_agreeing_pts(rf_1, message, self.x_coords) 
                        setTwo = self.find_agreeing_pts(rf_2, message, self.x_coords)
                        to_recon = setOne - setTwo 
                        poly_recon_att = lagr_reconstruct(message, to_recon, self._pR)
                        if compute_norm(poly_recon_att) <= self._ell:
                            nag_pts = len(self.find_agreeing_pts(poly_recon_att, message, self.x_coords))
                            if nag_pts >= self._agreement:
                                logger.info("Found polynomial in first part through error profile")
                                identify_poly_found(valid_polys, poly_recon_att)
                                return poly_recon_att
        return []    

    def search_basis(self, A, ub_on_sol,message):
        rpolys = self.check_sol_in_basis(A,ub_on_sol)
        if len(rpolys) != 0:                
            return rpolys
        #TODO: switch back
        #poly_recon_att = self.check_one_sol_out(A,ub_on_sol,message)
        #if len(poly_recon_att) != 0:
        #    return poly_recon_att

        return []

    # returns whether or not any points were removed
    def temp_remove_pts(self, A, x_indics, ub_on_sol, message):
        to_throw = None
        deg_soln = 0
        N = self.lagrInfo.get_N() 
        for row in A:
            if compute_norm(row) <= ub_on_sol:
                cur_factor = gcd(N, row[0])
                if cur_factor.degree() > deg_soln:
                    to_throw = cur_factor
                    deg_soln = cur_factor.degree()
        if deg_soln != 0:
            # I have to be more careful here to account for having already thrown something out 
            # (temporarily throw out points) 
            is_new = False
            implic_set = convert_poly_to_set(to_throw)           
            for idx,_ in enumerate(x_indics):
                if message[idx][0] in implic_set and x_indics[idx] == 1:
                    # NOT A COPY, THIS SHOULD BE A REFERNCE TO X_INDICS
                    x_indics[idx] = 2
                    is_new = True
            #ok bb, update the stuff
            self.lagrInfo.update(x_indics)
            return is_new
        else:
            # move on to the next step if you can't?  
            return False 

    def debug_funct(self, A, x_indics, message, ell, t, k):
        #ub_on_sol = x_indics.count(1) - self._agreement + ell
        # the target vector is error_poly**k*poly**t (I think)
        ub_on_sol = (x_indics.count(1)-self._agreement)*k + ell*t
        #construct small 
        A_sm = []
        if A.nrows() >= (self._c+1): 
            for row in A:
                if compute_norm(row) <= ub_on_sol:
                    A_sm.append(row)
            A_sm = Matrix(A_sm)
        else:
            A_sm = A
        if A_sm.nrows() == 0:
            logger.info("No rows, exiting this phase")
            return


        U_l = self.calculate_unimod(A_sm, x_indics, message, [0]*(self._c+1), t, k)
        # cull the points that are not strings
        U_lp = []
        kept_rows = []
        for i in range(len(U_l)):
            if U_l[i] != "Not in lattice":
                U_lp.append(U_l[i])
                kept_rows.append(i)
            else:
                logger.info("Solution {} not in lattice".format(i))
        U = Matrix(U_lp)
        # S = UPRIME * B
        # UPRIME MAY NOT BE SQUARE!!!
        if U.nrows() == 0:
            logger.info("No solution vectors in this basis")
            return 
        if U.nrows() != U.ncols():
            logger.info("ERROR: Not a square basis!")
            #logger.info("U' from S=U'*B, including too small vectors\n{}".format(compute_deg_mtx(U.change_ring(self._pR))))
            # build soln_mtx directly 
            # then build U from B = U * SOLN_MTX by using solve left maybe?            
            f_soln_mtx = self.create_full_soln_mtx(x_indics,message, [0]*(self._c+1), t, k)
            # build U from B = U * S
            # by left solving for
            built_U = []
            try: 
                for j in range(A_sm.nrows()):
                    comb = f_soln_mtx.solve_left(A_sm[j])
                    built_U.append(comb)
            except:
                return None
            built_U = Matrix(built_U).change_ring(self._pR)
            logger.info("WARNING, THIS IS B = U * S' FOR AN AUGMENTED S'")
            logger.info("FULL MATRIX DEGREES FOR U:\n{}".format(compute_deg_mtx(built_U)))
            return f_soln_mtx
        
        U_inv = U.inverse()
        U_inv_cp = []
        #.change_ring(self._pR)
        try:
            U_inv = U_inv.change_ring(self._pR)
            for j in range(U_inv.ncols()):
                U_inv_cp.append(compute_norm(U_inv.column(j)))
            logger.info("FULL MATRIX DEGREES FOR U:\n{}".format(compute_deg_mtx(U_inv)))
            logger.info("COLUMN PROFILE: {}".format(U_inv_cp))
        except:
            logger.info("NOTE! U_inv is not a poly. mtx!!")
            #logger.info("{}".format(U_inv)) 
            mimic_U_deg = Matrix(U_inv.nrows(),U_inv.ncols())
            for i in range(U_inv.nrows()):
                for j in range(U_inv.ncols()):
                    elt_c = U_inv[i][j]
                    mimic_U_deg[i,j] = elt_c.numerator().degree() - elt_c.denominator().degree()    
            logger.info("FULL MATRIX DEGREES FOR U:\n{}".format(mimic_U_deg))
        soln_mtx = U*A_sm
        logger.info("REDUCED BASIS RP: {}\nSOLN RP: {}".format(compute_row_profile(A_sm.change_ring(self._pR)),compute_row_profile(soln_mtx.change_ring(self._pR))))

        return soln_mtx

    # return a solution if you found it
    # and inf. on whether alg. should continue or stop 
    def find_one(self, x_indics, message, ell):
        clfs = True
        fas = False 
        #logger.info("STARTING OUTER LOOP")
        
        fs_nf = True
        at_least_one = False
      
        beg_ell = ell
        # new try, if the *difference* is 0 that's when you stop
        A = None
        sv_len = -1
        ub_on_sol = -1


        #################
        # NEED DEBUGGING HERE
        # TODO take this away but for now calculate it everytime 
        if DEBUG:
            test_shift = [ell] + [0]*self._c
            ub_on_sol = x_indics.count(1) - self._agreement + self._ell
            A = self.first_step(message, x_indics, test_shift)
            # problem here is this should be unweighted? 
            logger.info("This is before the loop!")
            A_sm = []
            for row in A:
                if compute_norm(row) <= ub_on_sol:
                    A_sm.append(row)
            A_sm = Matrix(A_sm)
            # re-setting ell off an upper bound here  
            sv_len_og = find_sv_len(A_sm) 
            
            if sv_len_og is not None:
                soln_mtx = self.debug_funct(A, x_indics, message, ell, 1, 1)
        #################        
         
        # do everything at once, no matter what. not efficient but should
        # be poly time. if *this* doesn't work, there's probably no easy change
        # that can be made to succeed in all instances  
        while fs_nf and ell >= 0:
            logger.info("USING {}".format(ell))
            for_pf = 0
            #TODO change back to 0 
            shifts = [ell] + [0] * self._c

            in_cond = True
            while in_cond:
                #trigger = False
                #if trigger:
                #    A_hm = self.test_dual_mult_shift(message, x_indics, shifts, 4, 3)
                #self.debug_funct(A_hm,x_indics,message,ell,3,2)  
                A = self.first_step(message, x_indics, shifts)
                # first simple check to see if there is potentially at least one solution
                sv_len = find_sv_len(A)
                ub_on_sol = x_indics.count(1) - self._agreement + ell
                
                if sv_len <= ub_on_sol:
                    # EASY CASE: Find a solution vector directly in the basis
                    pot_res = self.search_basis(A, ub_on_sol, message) 
                    if len(pot_res) != 0:
                        return (True, True, pot_res)
                else:
                    # pretty sure this is a failure condition
                    return (False, False, []) 
                
                # look at short rows to try and throw out points (take one of the rows with the biggest number of agreeing points)
                did_removal = self.temp_remove_pts(A, x_indics, ub_on_sol, message)
                if not did_removal:
                    in_cond = False 
                else:
                    ub_on_sol = x_indics.count(1) - self._agreement + ell
            logger.info("Going through second step".format(ell))
                 
            not_finished = True
            start_ell = ell
            while not_finished:
                ub_on_sol = x_indics.count(1) - self._agreement + ell
                first_run = False #True

                new_shifts = [ell] + [0]*self._c
                A = self.first_step(message, x_indics, new_shifts)
                A_sm = []
                for row in A:
                    if compute_norm(row) <= ub_on_sol:
                        A_sm.append(row)
                A_sm = Matrix(A_sm)
                num_vecs = A_sm.nrows()
                if DEBUG:
                    # DEBUG INFO #####
                    soln_mtx = self.debug_funct(A, x_indics, message, ell, 1, 1)
                    ##########################
                found_shifts = False
                while not found_shifts:
                    logger.info("What follows is for shift {}".format(new_shifts))
                    A, sh_deg, un_deg, piv = self.shifted_popov(A_sm, new_shifts)
                    if DEBUG:
                        s_m = self.debug_funct(A, x_indics, message, ell, 1, 1)
                        logger.info("Pivots are {}".format(piv))
                        if not s_m is None:
                            s_m = weight(s_m, new_shifts, self._z)
                            logger.info("\n{}".format(compute_deg_mtx(s_m.change_ring(self._pR))))
                            rdeg_s = sum(compute_row_profile(s_m.change_ring(self._pR)))
                            logger.info("Is S, {}-row reduced? Is rdeg(S) = {} = det(S) = {}?".format(new_shifts, rdeg_s, un_deg))
                        else:
                            logger.info("Could not check, last step something fell out of the lattice")
                    if not 0 in piv:
                        found_shifts = True

                        if DEBUG:
                            logger.info("Breaking")
                            # check if the soln_mtx *is* reduced 
                            s_m = self.debug_funct(A, x_indics, message, ell, 1, 1)
                            if not s_m is None:
                                s_m = weight(s_m, new_shifts, self._z)
                                logger.info("\n{}".format(compute_deg_mtx(s_m.change_ring(self._pR))))
                                rdeg_s = sum(compute_row_profile(s_m.change_ring(self._pR)))
                                logger.info("Is S, {}-row reduced? Is rdeg(S) = {} = det(S) = {}?".format(new_shifts, rdeg_s, un_deg))
                    else:
                        # increase all non-pivots, run again? 
                        for j in range(self._c+1):
                            if not j in piv:
                                new_shifts[j] += 1


                logger.info("State of shifts before check stage: {}".format(new_shifts))
                A, sh_deg4, un_deg4, piv4 = self.shifted_popov(A_sm, new_shifts)
                # check stage
                A_sm = [] 
                for row in A:
                    if compute_norm(row) <= ub_on_sol:
                        A_sm.append(row)
                A_sm = Matrix(A_sm)
                sv_len = find_sv_len(A_sm)  

                # TODO: CHECK THE BASIS FOR A VECTOR
                rpolys = self.search_basis(A_sm, ub_on_sol, message) 
                if len(rpolys) != 0:                
                    return (True, True, rpolys)
                # CHECK FOR MORE POINTS TO REMOVE 
                      
                did_removal = self.temp_remove_pts(A_sm, x_indics, ub_on_sol, message)
                # if you do this, you should probably restart (?) 
                if did_removal:
                    ub_on_sol = x_indics.count(1) - self._agreement + ell
                    continue

                all_points = set()
                for idx, is_present in enumerate(x_indics):
                    if is_present == 1:
                        all_points.add(message[idx][0]) 
                cnp = len(all_points)
                old_ap = all_points.copy()
                # VECTOR PREP FOR SECOND STEP
                logger.info("GOING THROUGH SECOND PART BECAUSE I HAVE TO")
                bvs = A_sm
                if bvs.nrows() <= 1:
                    # you can't even run this step 
                    #ell += 1
                    #continue
                    # going to assume this is a cause for termination
                    return (False, False, [])   
                search_pt = all_points.pop()

                err_term = (self._z - search_pt)
                list_pts = [search_pt]
                unconstr_pts = set()

                lpr = print_current_pt_distr(message, x_coords_list, list_pts, self._z, x_indics)
                
                weight_factor = self._z
                # calculate the current point distribution
                rows_to_add = self.alt_sublatt_solve(bvs, weight_factor, err_term)
                new_bvs = Matrix(rows_to_add)*bvs
                cat1 = ones_matrix(self._pR, 1, len(rows_to_add))
                total_vec = list(cat1*new_bvs)
                total_vec = total_vec[0].list()

                if DEBUG:
                    ###### DEBUG INFO #########
                    M, M_cp = calculate_mtx(soln_mtx, new_bvs, self._z, for_pf, self._pR)
                    logger.info("IN FIRST STEP WHAT IS THE SUPPORT:\n{}".format(compute_deg_mtx(M)))
                    logger.info("Column Profile") 
                    logger.info(M_cp)
                    ######################
                
 
                if total_vec[0] == self._pR(0):
                    logger.info("In reduction step total vector has first column 0, so rows to add probably returned nothing? not sure why")
                    logger.info("Treating this as a failure, maybe a mistake")
                    ag_pts = all_points
                else:
                    excl_poly = total_vec[1:]
                    excl_poly = [
                        (self._pR(x) / self._pR(total_vec[0]))
                        for x in excl_poly
                    ]

                    ag_pts = self.find_agreeing_pts(excl_poly, message, all_points)

                # did you not lose any other points but the ones you fixed on? if so, you need to do somet work
                loss = all_points - ag_pts
                recon_set = all_points.union(set([search_pt])) - ag_pts
                # first check if you can do anything with the recon set, if you can't then you need to continue 
                if len(recon_set) > 0:
                    if len(recon_set) < (self._ell+1) and len(loss) != 0:
                        # TODO: this is probably an unnecessary check 
                        logger.info("Recon set wasn't large enough, failing")
                        return (False, False, [])
                    poly_recon_att = lagr_reconstruct(message, recon_set, self._pR)
                    num_ag_pts = self.find_agreeing_pts(poly_recon_att,message, old_ap) 
                    if compute_norm(poly_recon_att) <= self._ell:
                        if len(num_ag_pts) > (self._ell +1):
                            #if len(num_ag_pts) >= self._agreement:
                            fas = True
                            logger.info("Found polynomial through lagrangian interpolation and reconstruction")
                            identify_poly_found(valid_polys, poly_recon_att)
                            return (clfs, fas, poly_recon_att)
                    else:
                        logger.info("Hit condition where recon_set > 0 but didn't recover anything")
                logger.info("Increasing the degree ell!")
                return (False, False, [])
                #not_finished = False
                #ell += 1
                #if ell >= self._c + start_ell:
                #    not_finished = False 
        return (False, False, [])

    def list_decode(self, message):
        # declare necessary globals
        self.solns = []
        global x_coords_list, valid_polys
        # record the degree profile of the solutions 
        for i in range(len(valid_polys)):
            res_vp = compute_deg_mtx(Matrix(valid_polys[i]))
            logger.info("Solution {} degree profile: {}".format(i,res_vp))

        if len(message) < self._agreement:
            return []
        
        self.x_coords = [m[0] for m in message]
        self.lagrInfo = LagrInterpol(self._pR, self._z, self.x_coords, self._c)
        self.N = self.lagrInfo.get_N()         
        x_indics = [1] * len(message)
        solns = []
        clfs = True  # continue-looking-for-solutions
        curr_ell = self._ell
        while clfs:
            if curr_ell < 0: 
                # couldn't find anything, quit. 
                break
            logger.info("Running with ell = {}".format(curr_ell))
            clfs, fas, sol_polys = self.find_one(x_indics, message, curr_ell)
            if fas:
                logger.info("Found a solution") 
                solns.append(sol_polys)
                self.solns.append(sol_polys)
                self.remove_pts(message, sol_polys, x_indics)
                # reset ell if it was moved 
                curr_ell = self._ell
            if clfs and not fas: 
                logger.info("Didn't work with current degree, trying {}".format(curr_ell-1))
                curr_ell -= 1
            if x_indics.count(1) < self._agreement:
                clfs = False  
        return solns


if __name__ == "__main__":
    Parallelism().set(nproc=8)
    parser = argparse.ArgumentParser()
    parser.add_argument("c", help="The number of polynomials to use", type=int)
    parser.add_argument("n", help="The total number of points to consider", type=int)
    parser.add_argument("ell", help="All chosen polynomials will be of degree <= ell", type=int)
    parser.add_argument("fs", help="Should be target *bit size* of field", type=int) 
    parser.add_argument(
        "agreement",
        help="The minimum necessary agreement for points to decode",
        type=int,
    )
    parser.add_argument(
        "--multiplicity",
        help="The multiplicty parameter of the decoding algorithm (default 1)",
        type=int,
        default=1,
    )
    parser.add_argument(
        "--shift",
        help="The shift parameter of the decoding algorithm (default 1)",
        type=int,
        default=1,
    )
    parser.add_argument(
        "--malic",
        help="Generate a simple malicious distribution - with solutions that collide on input points",
        action=argparse.BooleanOptionalAction,
    )
    parser.add_argument(
        "--malicspan",
        help="Generate another simple malicious distribution",
        action=argparse.BooleanOptionalAction,
    )
    parser.add_argument(
        "--debug",
        help="Generate additional debug information",
        action=argparse.BooleanOptionalAction,
    )
    parser.add_argument(
        "--distr",
        help="Specify the distribution that should be drawn from. There are 4 options, \"hard-gap\" (4), \"hard\"(3), \"close\"(2), \"easy\"(1), \"any\"(0)",
        type=int,
        default=0,
    )
    parser.add_argument(
        "--exact_distr",
        help="Specifies an exact distribution of errors and stalkers, this option has higher priority than distr. It should be a list where the last argument is the number of errors and the other positions each indicate a polynomial set and the number of points to create that agree with the set.",
    )
    parser.add_argument(
        "--file", 
        help="Another more flexible way to define an exact distribution for testing. This also allows testing an exact input codeword. It is expected that file is a json file, see INPUT_DISTR_FORMAT.txt for more info on its exact structure. This option overrides all other parameters given to the program. Override order is file, exact_distr, distr",
    )
    args = parser.parse_args()
    logging.basicConfig(filename="info.log", filemode='w',level=logging.INFO)

    fname = args.file
    DEBUG = False
    if "debug" in args:
        DEBUG = args.debug
    valid_polys = []
    input_words = []
    x_coords_list = []
    indics_to_recover = []
    list_stalkers = []
    if fname:
        # generate instance from file 
        d_config, indics_to_recover, input_distr, valid_polys, input_words, x_coords_list, x_coords = gen_special_inst(fname) 
        list_stalkers = input_distr[:-1]
        e = input_distr[-1]
    else:
        d_config = {
            "f_size": int(Integer(2 ** args.fs).previous_prime()),
            "c": args.c, 
            "n": args.n,
            "ell": args.ell,
            "agreement": args.agreement,
            "k": args.multiplicity, # field is useless for now
            "t": args.shift, # field is useless for now
        }
        d_config["_field"] = GF(d_config["f_size"])
        d_config["_pR"] = PolynomialRing(d_config["_field"], "z")
        
        if "malic" in args and args.malic:
            list_stalkers, valid_polys, input_words, x_coords_list, x_coords = gen_cross_inst(d_config["_field"],d_config["_pR"],d_config["c"],d_config["n"],d_config["ell"],d_config["agreement"])
            e = int(0)
            indics_to_recover = [int(0), int(1)]
        elif "malicspan" in args and args.malicspan:
            list_stalkers, valid_polys, input_words, x_coords_list, x_coords = gen_mult_inst(d_config["_field"],d_config["_pR"],d_config["c"],d_config["n"],d_config["ell"])
            indics_to_recover = [int(0), int(1)]
            e = int(len(x_coords))
        else: 
            distr_pick = args.distr
            exact_distr = args.exact_distr
        
            e = 0
            if exact_distr is not None:
                exact_d = json.loads(exact_distr)
                if type(exact_d) != list or len(exact_d) == 0:
                    print("Exact distribution is incorrectly encoded")
                    sys.exit(1)
                if sum(exact_d) != d_config["n"]:
                    print("Exact distribution does not add up to the number of input points n")
                    sys.exit(1)
                if len(exact_d) == 1:
                    e = exact_d[0]
                else:
                    list_stalkers = exact_d[:-1]
                    e = exact_d[-1]
            else:    

                poss_stalkers = int(math.floor(d_config["n"] / d_config["agreement"]))
                # change to always try for as many stalkers 
                # as possible 
                if distr_pick == 0:
                    # "any distr"
                    # only requirement at least one poly set 
                    num_stalkers = randint(1, poss_stalkers)
                    e = d_config["n"] - num_stalkers * d_config["agreement"]
                    list_stalkers = [d_config["agreement"]] * num_stalkers
                    for i in range(num_stalkers):
                        if e != 0:
                            add_xtra = randint(0,e)
                            e -= add_xtra
                            list_stalkers[i] += add_xtra
                elif distr_pick == 1:
                    # "easy distr" 
                    # one poly set 
                    num_stalkers = 1
                    e = d_config["n"] - d_config["agreement"]
                    list_stalkers = [d_config["agreement"]]
                    for i in range(num_stalkers):
                        if e != 0:
                            add_xtra = randint(0,e)
                            e -= add_xtra
                            list_stalkers[i] += add_xtra
                elif distr_pick == 2:
                    # "close distr"
                    # poly sets with close to same number of points
                    num_stalkers = poss_stalkers 
                    e = d_config["n"]-num_stalkers*d_config["agreement"]
                    list_stalkers = [d_config["agreement"]] * num_stalkers
                    divide_at = randint(1,num_stalkers)
                    if e >= divide_at:
                        for i in range(divide_at):
                            list_stalkers[i] += 1
                        e -= divide_at
                    else:
                        top_off = min(e,num_stalkers)
                        for i in range(top_off):
                            list_stalkers[i] += 1
                        e -= top_off
                elif distr_pick == 4:
                    # hard *gap* 
                    # numerous polys with points between k and t 
                    num_stalkers = randint(1, poss_stalkers)
                    num_gap = randint(0,poss_stalkers-num_stalkers)
                    list_stalkers = [d_config["agreement"]] * num_stalkers
                    e = d_config["n"] - (num_gap+num_stalkers)*d_config["agreement"]
                    for i in range(num_gap):
                        shave_off = randint(1,4)
                        e += shave_off
                        list_stalkers.append(d_config["agreement"]-shave_off)
                    
                else: 
                    # "hard distr"    
                    # all poly sets w. same number of points
                    num_stalkers = poss_stalkers 
                    e = d_config["n"]-num_stalkers*d_config["agreement"]
                    list_stalkers = [d_config["agreement"]] * num_stalkers
        # indices for polys that should be recovered 
        indics_to_recover = []
        e = int(e)
        for i in range(len(list_stalkers)):
            list_stalkers[i] = int(list_stalkers[i])
            if list_stalkers[i] >= d_config["agreement"]:
                indics_to_recover.append(i)    
        valid_polys, input_words, x_coords_list, x_coords = gen_adversarial_instance(
            d_config["_field"], d_config["_pR"], d_config["ell"], d_config["c"], list_stalkers + [e]
            )
        
    # Setup decoder
    S = PolynomialRing(d_config["_pR"], d_config["c"], "x", order="lex")
    xs = S.monomials_of_degree(1)
    decoder = CHDecoder(d_config["_pR"], d_config["c"], 
        d_config["n"], d_config["ell"], d_config["agreement"])

    #shuffle(input_words)
    if not is_unique(input_words):
        raise Exception("x-coordinates are not unique")

    # THIS IS A "FIX IT UP" or "DOUBLE CHECK" STEP 
    # Flag the program if x_coords_list is incorrect for any real poly
    xc = [word[0] for word in input_words] 
    for i in range(0, len(valid_polys)):
        # check is the agreement right?
        ag_pts = decoder.find_agreeing_pts(valid_polys[i], input_words, xc)     
        poly_test = decoder._pR(1)
        for pt in ag_pts:
            poly_test *= (decoder._z - pt)
        if poly_test != x_coords_list[i]:
            x_coords_list[i] = poly_test
            #print("ERROR: IN X_COORDS_LIST {}".format(i))
            #raise Exception("QUITTING...")
            
    write_to_file("last_run.json", input_words, valid_polys, x_coords_list, x_coords, d_config["ell"]) 
    logger.info("NEW RUN")
    list_sol = []
    start_time = time.time()
    #try:
    list_sol = decoder.list_decode(input_words)
    #except Exception as ex:
    #    logger.info(ex) 
    dur_full = time.time() - start_time

    all_present = True
    is_covered = []

    # every valid poly must be recovered
    for idx in indics_to_recover:
        poly_set = valid_polys[idx]
        if not poly_set in list_sol:
            # failure 
            all_present = False
            break
    logger.info("FINAL OUTPUT")
    if all_present:
        logger.info("Success")
    else:
        logger.info("Failure")
        write_to_file("failure.json", input_words, valid_polys, x_coords_list, x_coords, d_config["ell"]) 
            

    num_sols_found = len(list_sol)
   
    # return some output
    result = (
        dur_full,
        all_present,
        num_sols_found,
        list_stalkers,
        int(e),
    )
    res_str = json.dumps(result)
    print(res_str)
