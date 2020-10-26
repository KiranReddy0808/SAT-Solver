import sys
import copy
import time

#parse the file for clauses
def file_parse(finput):
    lines = open(finput,'r').readlines()
    eq = []
    firstline = lines[0].split()

    #number of variables is stored
    novar = int(firstline[2])
   
    #append clauses as lists
    for line in lines[1:]:
        temp = []
        temp = [int(x) for x in line.split()]
        temp.pop()
        eq.append(temp)

    return eq,novar


def CDCL(eq,novar):

    #v stores variables in [no.,0/1,descisionlevel] format
    v = []

    #antecedent clause is stored as dict the corressponding value stored is index in eq
    anc_cl = {}

    #Used to check if all variables are assigned
    var = []
    total = []
    total = [x for x in range(1,novar+1)]

    #Descision level
    dl = 0

    #learned clause count
    lc_count = 0

    #implications count
    imp_count = 0

    #descisions count
    des_count = 0

    #conflict counter
    confl_count = 0


    #If the equation contains unary clauses add them to v
    for item in eq:
        if len(item) == 1:
            if item[0] < 0:
                x = -1*int(item[0])
                v.append([x,0,0])
                anc_cl[-1*x] = -1
            else:
                x = int(item[0])
                v.append([x,1,0])
                anc_cl[x] = -1

    #Preprocessing deletion of clauses which will be always be satisfiable
    #except the unary clause for 0 dl vars
    eq = pre_del(eq,v)
    if eq == []:
        return 'SAT',0,0,imp_count

    #initalize literal frequency and literal polarizarion
    lit_freq= [0 for x in range(1,novar+1)]
    lit_pol=[0 for x in range(1,novar+1)]

    #find the values of literal frequency 
    # and literal polarization
    for clause in eq:
        for literal in clause:
            if literal > 0:
                lit_freq[literal-1] = lit_freq[literal-1] + 1
                lit_pol[literal-1] = lit_pol[literal-1] + 1
                
            if literal < 0:
                lit_freq[-1*literal-1] = lit_freq[-1*literal-1] + 1
                lit_pol[-1*literal-1] = lit_pol[-1*literal-1] - 1
    
    #store the original values in another list
    orig_lit_freq = copy.deepcopy(lit_freq)
                
    #detect conflict at descision level 0
    x,v,anc_cl,imp_count = confl_Detect(eq,v,anc_cl,dl,imp_count)
    if x == 0:
        return 'UNSAT',0,0,imp_count

    #When all variables are assigned 
    #var becomes same as list total and loop stops
    while var != total:           
        
        #increment descision level
        dl = dl+1

        #decide new variable, assign antecedent 
        # and increment descision count
        new_var,sign,lit_freq,orig_lit_freq = decide(var,novar,lit_freq,lit_pol,orig_lit_freq,confl_count)
        if sign == 0:
            anc_cl[-1*new_var] = -1
        else:
            anc_cl[new_var] = -1
        v.append([new_var,sign,dl])
        des_count = des_count + 1 
        
        
        x,v,anc_cl,imp_count = confl_Detect(eq,v,anc_cl,dl,imp_count)
        while x == 0:

            confl_count = confl_count + 1

            #Analyse conflict and get learnt clause and level to backtrack
            b,c = confl_Anal(eq,v,anc_cl,dl)

            #add the new clause if not already in eq
            if c not in eq:
                eq.append(c)

                #increment learned clauses count
                lc_count = lc_count + 1

            #conflict occured for variable whose dl = 0 then b<0
            if b < 0:
                return 'UNSAT',lc_count,des_count,imp_count

            else:
                 
                #backtrack to the level b and assign b as dl
                v,anc_cl,b,lit_freq = backtrack(v,b,anc_cl,lit_freq,orig_lit_freq)
                dl = b

                #if a unary clause is learnt add it to v
                if len(c) == 1:
                    if c[0] < 0:
                        z = -1*int(c[0])
                        v.append([z,0,0])
                        anc_cl[-1*z] = -1
                    else:
                        z = int(c[0])
                        v.append([z,1,0])
                        anc_cl[z] = -1
                
                #update new frequency from learned clause
                lit_freq,orig_lit_freq,lit_pol = update_freq(c,lit_freq,orig_lit_freq,lit_pol)

            #analyse conflict while remaining in while loop
            x,v,anc_cl,imp_count = confl_Detect(eq,v,anc_cl,dl,imp_count)

        #update var from all the variables in v
        var = update_var(v)

    return 'SAT',lc_count,des_count,imp_count


#function to find new variable to assign
def decide(var,novar,lit_freq,lit_pol,orig_lit_freq,confl_count):

    #assign frequency for variables in var
    for i in var:
        if lit_freq[i-1] != -1:
            lit_freq[i-1] = -1

    #decay the frequency as the 
    #number of conflicts reach 100
    if confl_count > 100:
        confl_count = confl_count%100
        for i in range(0,novar):
            orig_lit_freq[i] = orig_lit_freq[i]/2
            if lit_freq[i] != -1 :
                lit_freq[i] = lit_freq[i]/2

    #find the index with maximum frequency
    var = lit_freq.index(max(lit_freq))

    #assign sign based on polarisation value
    if lit_pol[var] > 0:
        sign = 1
    else:
        sign = 0

    return var+1,sign,lit_freq,orig_lit_freq

#Function to update frequency
def update_freq(clause,lit_freq,orig_lit_freq,lit_pol):

    #for the literals in learnt clause, 
    #update literal frequency and polarisation values
    for literal in clause:
            if literal > 0:
                lit_freq[literal-1] = lit_freq[literal-1] + 1
                lit_pol[literal-1] = lit_pol[literal-1] + 1
                
            if literal < 0:
                lit_freq[-1*literal-1] = lit_freq[-1*literal-1] + 1
                lit_pol[-1*literal-1] = lit_pol[-1*literal-1] - 1

    return lit_freq,orig_lit_freq,lit_pol

#function to detect the Conflict
def confl_Detect(eq,v,anc_cl,dl,imp_count):

    #copy the contents of eq
    eq_copy = []
    eq_copy = copy.deepcopy(eq)

    for i in v:
        # z represents the negated value of the variable in v
        z = int(i[0])
        if i[1] == 1:
            z = -1*z
        # index is used to find the index of clause which is ancedent for a new variable which will be added
        index = -1
        for lis in eq_copy:
            index = index + 1
            #if -z exists means satisfiable clauses
            if -1*z in lis:
                lis = []
                lis.append(-1*z)
            #if the value exists remove from lis
            if z in lis:
                lis.remove(z)
            #if a variable is implied add to v and set its antecedent clause
            if len(lis) == 1:
                x = lis[0]
                y,v = check(x,v,dl)
                if y == 1 and lis[0] != -1*z:
                    imp_count = imp_count + 1
                    anc_cl[x] = index
            #if a conflict is detected 
            if len(lis) == 0:
                anc_cl[0] = index
                return 0,v,anc_cl,imp_count

    return 1,v,anc_cl,imp_count            

#Function for conflict analysis
def confl_Anal(eq,v,anc_cl,dl):
    conf_l = 0
    b = 0

    # copy the antecedent of conflict to lis
    lis = copy.deepcopy(eq[anc_cl[0]])

    # conf_l stores the descision level of conflict 
    for i in lis:
        for j in v:
            if j[0] == abs(i) and conf_l < j[2]:
                conf_l = j[2]
    
    # if conflict occured at descision level 0 return -1
    if conf_l == 0:
        return -1,[]

    # store number of literals found from same descision level
    count = 0
    while(1):
        count = 0

        #iterate over all the literals to find UIP
        for i in lis:
            for j in v:
                if j[0] == abs(i) and j[2] == conf_l:
                    count = count+1

                #ancedent of resol will be used to resolve and find UIP
                if j[0] == abs(i) and j[2] == conf_l and anc_cl[-1*i] != -1:
                    resol = i
        
        # implies we reached descision variable and its the UIP
        if count == 1:
            break

        #store the antecedent and resolve
        ante = eq[anc_cl[-1*resol]]
        lis = resolve(ante,lis,resol)

    #finding the asserting level
    for item in lis:
        for i in v:
            if i[0] == abs(item) and conf_l > i[2] and b < i[2]:
                b = i[2]
    
    return b,lis

#delete the useless clauses
def pre_del(eq,v):
    rem = []

    #iterate over all variables
    for i in v:
        z = int(i[0])
        if i[1] == 0:
            z = -1*z
        
        #clauses containing the literal same 
        # as the assignment of variable are 
        # useless as they are always 1 expect unary
        for lis in eq:
            if z in lis and len(lis) != 1: 

                #append all the clauses from the list
                rem.append(lis)

    #duplicates might appear 
    # which need to be removed
    rem_dupl = []
    for lis in rem:
        if lis not in rem_dupl:
            rem_dupl.append(lis)

    #remove the clauses
    for i in rem_dupl:
        eq.remove(i)
    return eq

#function to perform resolve
def resolve(ante,lis,x): 
    
    #copy the two lists into new lists
    new_lis = copy.deepcopy(ante)
    temp = copy.deepcopy(lis)

    #create new list and apply binary resolution rule
    merge = []

    for i in new_lis:
        merge.append(i)
    for i in temp:
        merge.append(i)
    merge.remove(x)
    merge.remove(-1*x)

    # remove duplicates from the list
    res = [] 
    for i in merge: 
        if i not in res: 
            res.append(i)

    return res
    

#function to implement backtrack
def backtrack(v,b,anc_cl,lit_freq,orig_lit_freq):

    # create a list to store all the 
    # variables which needs to be removed
    rem = []

    #iterate over v to find all the variables
    #with dl greater than b and also remove antecedent
    for i in v:
        x = i[0]
        if i[1] == 0:
            x = -1*x
        if i[2] >= b:
            rem.append(i)
            if x in anc_cl.keys():
                del anc_cl[x]

    #remove literals
    for j in rem:
        v.remove(j)
        lit_freq[j[0]-1] = orig_lit_freq[j[0]-1]
        

    #remove the antecedent of the conflict
    del anc_cl[0]

    return v,anc_cl,b,lit_freq

#function to check if the literal is already in v
def check(x,v,dl):

    #store the literal value
    if x < 0:
        z = -1*x
    else:
        z = x
    
    #literal is found return 0
    for j in v:
        if j[0] == z and x<0 and j[1] == 0:
            return 0,v
        if j[0] == z and x>0 and j[1] == 1:
            return 0,v
    
    #if not found append and return 1
    if x < 0:
        v.append([z,0,dl])
    else:
        v.append([z,1,dl])
    return 1,v

#function to update number of variables from v
def update_var(v):

    #update var for every element var doesn't 
    #contain and v contains
    var = []
    for i in v:
        if i[0] not in var:
            var.append(i[0])
    var.sort()
    return var






#start the timer
start = time.time()

finput = sys.argv[1]
eq,novar = file_parse(finput)

#Apply the CDCL algorithm and print the output  
output,lc_count,des_count,imp_count = CDCL(eq,novar)

#end the timer and calculate the runtime
end = time.time()

print(f'Number of Variables: {novar}')
print(f'Number of Clauses: {len(eq) - lc_count}')
print(f'Assignment: {output}')
print(f'Learned Clauses: {lc_count}')
print(f'Descisions: {des_count}')
print(f'Implications: {imp_count}') 
print(f'Runtime: {end - start}s')
