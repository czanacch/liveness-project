import pynusmv
import sys

def spec_to_bdd(model, spec):
    """
    Return the set of states of `model` satisfying `spec`, as a BDD.
    """
    bddspec = pynusmv.mc.eval_ctl_spec(model, spec)
    return bddspec

# Da un certo punto in poi vale sempre la proprietà!
def check_persistently(spec):

    '''
    if check_repeatedly(~spec) == check_repeatedly(spec):
        return False
    '''

    if check_repeatedly(~spec) == False:
        return True
    else:
        return False


def check_repeatedly(spec):
    mod = pynusmv.glob.prop_database().master.bddFsm # Riferimento al modello caricato

    Init = mod.init # Insieme Init degli stati iniziali
    Trans = mod.trans # Insieme delle transizioni (il tipo è BDDTrans, che include l'operatore PRE e POST)

    bddSpec = spec_to_bdd(mod, spec) # riferimento alla negazione della proprietà

    # Symbolic Breadth-First-Search Algorithm
    Reach = Init
    New = Init
    while New.size != 1:
        New = Trans.post(New).diff(Reach)
        Reach = Reach.or_(New)

    # Da questo punto in poi abbiamo l'insieme Reach degli "stati raggiungibili"
    
    Recur = Reach.and_(bddSpec) # Ottengo Recur_0
    
    while Recur.size != 1: # finchè l'insieme Recur non è vuoto
        
        Reach = pynusmv.dd.BDD.false() # BDD vuoto

        New_2 = Trans.pre(Recur) # New sono gli stati precedenti da cui si arriva da Recur

        # è un "do-while"
        Reach = Reach.or_(New_2) # Unione di reach con new
        if Recur.leq(Reach):
            return True
        New_2 = Trans.pre(New_2).diff(Reach)

        while New_2.size != 1: # Finchè l'insieme New non è vuoto
            Reach = Reach.or_(New_2) # Unione di reach con new
            if Recur.leq(Reach):
                return True
            New_2 = Trans.pre(New_2).diff(Reach)

        Recur = Reach.and_(Recur)

    return False

if len(sys.argv) != 2:
    print("Usage:", sys.argv[0], "filename.smv")
    sys.exit(1)

pynusmv.init.init_nusmv()
filename = sys.argv[1]
pynusmv.glob.load_from_file(filename)
pynusmv.glob.compute_model()
invtype = pynusmv.prop.propTypes['Invariant']
for prop in pynusmv.glob.prop_database():
    spec = prop.expr
    if prop.type == invtype:
        print("Property", spec, "is an INVARSPEC.")

        res = check_persistently(spec)
        if res == True:
            print("Property is persistent")
        else:
            print("Property is not persistent")

        res = check_repeatedly(spec)
        if res == True:
            print("Property is recurrent")
        else:
            print("Property is not recurrent")

    else:
        print("Property", spec, "is not an INVARSPEC, skipped.")

pynusmv.init.deinit_nusmv()