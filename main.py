from __future__ import division, print_function
from math import factorial, ceil
from itertools import product, combinations, permutations
import pylgl
from sys import stderr
from tqdm import tqdm
from copy import deepcopy
from caching import cache
from helperfunctions import *

# necessary for converting python objects to ints (which pylgl wants)
# also for transforming back
litcount = 0
lit2int = {}
int2lit = {}

def posLiteral(committee, profile):
    global litcount, lit2int, int2lit

    if (committee, profile) in lit2int:
        return lit2int[(committee, profile)]
    else:
        litcount+=1
        lit2int[(committee, profile)] = litcount
        int2lit[litcount] = (committee, profile)
        return litcount

def negLiteral(committee, profile):
    return -posLiteral(committee, profile)

def cnfPAV():
    """
    Calculates the PAV score, and returns a negative literal for those
    committees that do not maximize it.

    Not as fast as it can be, but clear and not a bottleneck.
    """


    cnf  = []
    for p in tqdm(list(allProfiles())):
        for k in ks:
            comscore = []
            # get all scores
            for c in allCommitteesOfSize(k):
                score = PAVscore(p,c)
                comscore.append((c, score))
            # calculate the maximum score
            maxscore = 0
            for c,s in comscore:
                maxscore = max(maxscore, s)
            # add all suboptimal committees as neglits
            for c,s in comscore:
                if s + 1e-5 < maxscore:
                    cnf.append([negLiteral(c,p)])
    return cnf


def cnfNeutrality():
    """
    Enforces neutrality, that is, a permutation of alternatives in the
    profile should not give a different result, except for applying the same
    permutation to the committee
    """
    cnf = []

    permDict = {}
    for p in allProfiles():
        for c in allCommittees():
            if p in permDict:
                continue
            for perm in candidatePerms(p, c):
                permDict[perm] = (p, c)

    for p in allProfiles():
        for c in allCommittees():
            permP = permDict[(p, c)][0]
            permC = permDict[(p, c)][1]

            cnf.append([negLiteral(c, p), posLiteral(permC, permP)])
            cnf.append([posLiteral(c, p), negLiteral(permC, permP)])

    return cnf

def cnfAnonymity():
    """
    Any permutation of the ballot should give the same committees
    """
    cnf = []
    for p in allProfiles():
        for c in allCommittees():
            sp = sortedProfile(p)
            cnf.append([negLiteral(c, p), posLiteral(c, sp)])
            cnf.append([posLiteral(c, p), negLiteral(c, sp)])
    return cnf

@cache("cnf_stratproof_n{}m{}k0{}k1{}.pickle".format(n,m,k0,k1))
def cnfStrategyproofness():
    """
    This axiom currently works according to "Strategyproofness" in D. Peters' 
    paper, and therefore (might) assume resoluteness
    """
    cnf = []
    for p1 in tqdm(list(allProfiles())):
        for i in allVoters():

            for p2 in ivariants(i, p1):
                if isSubsetOf(p2[i], p1[i]):
                    for c1 in allCommittees():
                        k = sum(c1)
                        for c2 in allCommitteesOfSize(k):
                            if strictlyBetter(i, c1, c2, p1):
                                cnf.append([negLiteral(c1, p1), negLiteral(c2, p2)])
    return cnf

@cache("cnf_kelly_card_stratproof_n{}m{}k0{}k1{}.pickle".format(n,m,k0,k1))
def cnfKellyCardinalityStrategyproofness():
    """
    Cardinality-strategyproofness for Kelly ranking of sets
    """
    cnf  = []
    for p1 in tqdm(list(allProfiles())):
        for i in allVoters():
            for p2 in ivariants(i,p1):
                for c2 in allCommittees():
                    k = sum(c2)
                    card = cardinalityOfOverlap(p1[i], c2)
                    for c1 in allCommitteesOfSize(k):
                        if cardinalityOfOverlap(p1[i], c1) < card:
                            clause = [negLiteral(c2, p2), negLiteral(c1, p1)]
                            cnf.append(clause)
    return cnf


@cache("cnf_kelly_superset_stratproof_n{}m{}k0{}k1{}.pickle".format(n,m,k0,k1))
def cnfKellySupersetStrategyproofness():
    """
    Superset-strategyproofness for Kelly ranking of sets
    """
    cnf = []
    for p1 in tqdm(list(allProfiles())):
        for i in allVoters():
            for p2 in ivariants(i, p1):
                for c1 in allCommittees():
                    k = sum(c1)
                    for c2 in allCommitteesOfSize(k):
                        if strictlyBetter(i, c1, c2, p1):
                            clause = [negLiteral(c1, p1), negLiteral(c2, p2)]
                            cnf.append(clause)
    return cnf


@cache("cnf_kelly2_card_stratproof_n{}m{}k0{}k1{}.pickle".format(n,m,k0,k1))
def cnfKelly2CardinalityStrategyproofness():
    """
    Cardinality-strategyproofness for Kelly ranking of sets
    This is an alternative way of generating the clauses that should be
    equivalent to cnfKellyCardinalityStrategyproofness
    """
    cnf = []
    for p1 in tqdm(list(allProfiles())):
        for i in allVoters():
            for p2 in ivariants(i,p1):
                for c1 in allCommittees():
                    k = sum(c1)

                    card = cardinalityOfOverlap(p1[i], c1)
                    for c2 in allCommitteesOfSize(k):
                        if cardinalityOfOverlap(p1[i], c2) > card:
                            clause = [negLiteral(c1, p1), negLiteral(c2, p2)]
                            cnf.append(clause)
    return cnf

@cache("cnf_optim_card_stratproof_n{}m{}k0{}k1{}.pickle".format(n,m,k0,k1))
def cnfOptimisticCardinalityStrategyproofness():
    """
    Cardinality-strategyproofness with respect to optimistic voters
    """
    cnf  = []
    for p1 in tqdm(list(allProfiles())):
        for i in allVoters():
            for p2 in ivariants(i,p1):
                for c2 in allCommittees():
                    k = sum(c2)
                    clause = [negLiteral(c2, p2)]
                    card = cardinalityOfOverlap(p1[i], c2)
                    for c1 in allCommitteesOfSize(k):
                        if cardinalityOfOverlap(p1[i], c1) >= card:
                            clause.append(posLiteral(c1, p1))
                    cnf.append(clause)
    return cnf

@cache("cnf_pess_card_stratproof_n{}m{}k0{}k1{}.pickle".format(n,m,k0,k1))
def cnfPessimisticCardinalityStrategyproofness():
    """
    Cardinality-strategyproofness with respect to pessimistic voters
    """
    cnf = []
    for p1 in tqdm(list(allProfiles())):
        for i in allVoters():
            for p2 in ivariants(i,p1):
                for c1 in allCommittees():
                    k = sum(c1)
                    clause = [negLiteral(c1, p1)]
                    card = cardinalityOfOverlap(p1[i], c1)
                    for c2 in allCommitteesOfSize(k):
                        if cardinalityOfOverlap(p1[i], c2) <= card:
                            clause.append(posLiteral(c2, p2))
                    cnf.append(clause)
    return cnf

@cache("cnf_optim_superset_stratproof_n{}m{}k0{}k1{}.pickle".format(n,m,k0,k1))
def cnfOptimisticSupersetStrategyproofness():
    """
    Superset-strategyproofness with respect to optimistic voters
    """
    cnf = []
    for p1 in tqdm(list(allProfiles())):
        for i in allVoters():
            for p2 in ivariants(i, p1):
                for c2 in allCommittees():
                    k=sum(c2)
                    clause = [negLiteral(c2, p2)]
                    for c1 in allCommitteesOfSize(k):
                        if not strictlyBetter(i, c1, c2, p1):
                            clause.append(posLiteral(c1, p1))
                    cnf.append(clause)
    return cnf

@cache("cnf_pess_superset_stratproof_n{}m{}k0{}k1{}.pickle".format(n,m,k0,k1))
def cnfPessimisticSupersetStrategyproofness():
    """
    Superset-strategyproofness with respect to pessimistic voters
    """
    cnf = []
    for p1 in tqdm(list(allProfiles())):
        for i in allVoters():
            for p2 in ivariants(i, p1):
                for c1 in allCommittees():
                    k = sum(c1)
                    clause = [negLiteral(c1, p1)]
                    for c2 in allCommitteesOfSize(k):
                        if not strictlyBetter(i, c1, c2, p1):
                            clause.append(posLiteral(c2, p2))
                    cnf.append(clause)
    return cnf

@cache("cnf_optim_subset_stratproof_n{}m{}k0{}k1{}.pickle".format(n,m,k0,k1))
def cnfOptimisticSubsetStrategyproofness():
    """
    Subset-strategyproofness with respect to optimistic voters

    This corresponds to Peter's strategyproofness, but adapted for optimistic voters in the irresolute case
    """
    cnf = []
    for p1 in tqdm(list(allProfiles())):
        for i in allVoters():
            for p2 in ivariants(i, p1):
                # if i's ballot is not a strict subset, 
                # this axiom does nothing
                if not isSubsetOf(p2[i], p1[i]):
                    continue
                for c2 in allCommittees():
                    k=sum(c2)
                    clause = [negLiteral(c2, p2)]
                    for c1 in allCommitteesOfSize(k):
                        if not strictlyBetter(i, c1, c2, p1):
                            clause.append(posLiteral(c1, p1))
                    cnf.append(clause)
    return cnf

@cache("cnf_pess_subset_stratproof_n{}m{}k0{}k1{}.pickle".format(n,m,k0,k1))
def cnfPessimisticSubsetStrategyproofness():
    """
    Subset-strategyproofness with respect to pessimistic voters

    This corresponds to Peter's strategyproofness, but adapted for pessimistic voters in the irresolute case
    """
    cnf = []
    for p1 in tqdm(list(allProfiles())):
        for i in allVoters():
            for p2 in ivariants(i, p1):
                # if i's ballot is not a strict subset, 
                # this axiom does nothing
                if not isSubsetOf(p2[i], p1[i]):
                    continue
                for c1 in allCommittees():
                    k = sum(c1)
                    clause = [negLiteral(c1, p1)]
                    for c2 in allCommitteesOfSize(k):
                        if not strictlyBetter(i, c1, c2, p1):
                            clause.append(posLiteral(c2, p2))
                    cnf.append(clause)
    return cnf

def cnfWeakParetoEfficiency():
    """
    Don't return a committee if there is another committee where every
    voter gets a superset of their approved candidates in the committee,
    and at least one strict superset
    """
    cnf=[]
    for profile in tqdm(list(allProfiles())):
        for k in ks:
            for committee1 in allCommitteesOfSize(k):
                for committee2 in allCommitteesOfSize(k):
                    if strictlySupersetDominates(profile, committee1, committee2):
                        cnf.append([negLiteral(committee2, profile)])
    return cnf


@cache("cnf_proportionality_n{}m{}k0{}k1{}.pickle".format(n,m,k0,k1))
def cnfProportionality():
    """
    Corresponds to Peters' weakest proportionality axiom, which he calls 
    "proportionality"

    In the irresolute case, states that all winners should satisfy
    proportionality
    """
    cnf = []
    for p in tqdm(list(allProfiles())):
        if isPartylistProfile(p):
            for a in allAlternatives():
                for k in ks:
                    if p.count(singletonBallot(a)) >= n/k-1e-5:
                        for c in allCommitteesOfSize(k):
                            if not c[a]:
                                cnf.append([negLiteral(c, p)])
    return cnf

def cnfJustifiedRepresentation():
    """
    Enforces justified representation (from the Aziz paper), in irresolute case: all winners must satisfy
    """
    cnf = []
    for p in tqdm(list(allProfiles())):
        for c in allCommittees():
            if not satisfiesJR(c, p):
                cnf.append([negLiteral(c,p)])
    return cnf


def cnfExtendedJustifiedRepresentation():
    """
    In irresolute case: all winners must satisfy
    """
    cnf = []
    for p in tqdm(list(allProfiles())):
        for c in allCommittees():
            if not satisfiesEJR(c, p):
                cnf.append([negLiteral(c,p)])
    return cnf


def cnfAtLeastOne():
    """
    Every profile should give at least a single winning committee
    """
    cnf = []
    for r in tqdm(list(allProfiles())):
        for k in ks:
            clause = []
            for c in allCommitteesOfSize(k):
                clause.append(posLiteral(c, r))
            cnf.append(clause)
    return cnf


def cnfResolute():
    """
    Every profile should give exactly one winner
    """
    cnf = []
    for r in tqdm(list(allProfiles())):
        for k in ks:
            for c1,c2 in combinations(allCommitteesOfSize(k), 2):
                cnf.append([negLiteral(c1, r), negLiteral(c2, r)])
    return cnf


def cnfParetoEfficiency():
    """
    Cardinality-based pareto, dont give committees that are dominated
    """
    cnf=[]
    for profile in tqdm(list(allProfiles())):
        for k in ks:
            for committee1 in allCommitteesOfSize(k):
                for committee2 in allCommitteesOfSize(k):
                    if strictlyDominates(profile, committee1, committee2):
                        cnf.append([negLiteral(committee2, profile)])
    return cnf


def cnfCommitteeMonotonicity():
    """
    No candidate should be a part of the committee if k=x, but not k=x+1.
    Largely untested
    """
    cnf  = []

    for profile in tqdm(list(allProfiles())):    
        
        # from k to k+1
        for k in ks[:-1]:
            for c1 in allCommitteesOfSize(k):
                clause = [negLiteral(c1, profile)]
                for c2 in allCommitteesOfSize(k+1):
                    if isSubsetOf(c1, c2):
                        clause.append(posLiteral(c2, profile))
                cnf.append(clause)

        # from k+1 to k
        for k in ks[1:]:
            for c1 in allCommitteesOfSize(k):
                clause = [negLiteral(c1, profile)]
                for c2 in allCommitteesOfSize(k-1):
                    if isSubsetOf(c2, c1):
                        clause.append(posLiteral(c2, profile))
                cnf.append(clause)
    return cnf


def cnfTiebreakInFavorOfMoreVotes():
    """
    Only allows ties (irresolute) between committees with the same AV score
    """
    cnf = []
    for profile in tqdm(list(allProfiles())):
        for k in ks:
            for committee1 in allCommitteesOfSize(k):
                for committee2 in allCommitteesOfSize(k):
                    if votesForCommittee(profile, committee1) != votesForCommittee(profile, committee2):
                        cnf.append([negLiteral(committee1, profile), negLiteral(committee2, profile)])
    return cnf


# leave this for reasons (specifically, ensuring that 
# literals still mean the same thing for cached results)
cnfAtLeastOne()


if __name__ == '__main__':
    
    """
    indicate here which axioms to use. For example, uncommenting
    atleastone, proportionality, paretoefficiency and some strategyproofness
    for optimistic and pessimistic voters gives out main result
    """
    
    cnf = []
    print("cnfAtLeastOne:", file=stderr)
    cnf += cnfAtLeastOne()
    #print("cnfResolute:", file=stderr)
    #cnf += cnfResolute()
    #print("cnfStrategyproofness:", file=stderr)
    #cnf += cnfStrategyproofness()
    #print("cnfAnonymity", file=stderr)
    #cnf += cnfAnonymity()
    print("cnfNeutrality", file=stderr)
    cnf += cnfNeutrality()
    #print('cnfProportionality:', file=stderr)
    #cnf += cnfProportionality()
    #print("cnfPAV")
    #cnf += cnfPAV()
    #print("cnfJustifiedRepresentation", file=stderr)
    #cnf += cnfJustifiedRepresentation()
    #print("cnfExtendedJustifiedRepresentation", file=stderr)
    #cnf += cnfExtendedJustifiedRepresentation()
    #print("cnfPessimisticCardinalityStrategyproofness", file=stderr)
    #cnf += cnfPessimisticCardinalityStrategyproofness()
    #print('cnfOptimisticCardinalityStrategyproofness', file=stderr)
    #cnf += cnfOptimisticCardinalityStrategyproofness()
    #print("cnfCommitteeMonotonicity:", file=stderr)
    #cnf += cnfCommitteeMonotonicity()
    #print("cnfParetoEfficiency", file=stderr)
    #cnf += cnfParetoEfficiency()
    #print("cnfTiebreakInFavorOfMoreVotes")
    #cnf += cnfTiebreakInFavorOfMoreVotes()
    #print("cnfWeakParetoEfficiency")
    #cnf += cnfWeakParetoEfficiency()
    #print("cnfOptimisticSupersetStrategyproofness")
    #cnf += cnfOptimisticSupersetStrategyproofness()
    #print("cnfPessimisticSupersetStrategyproofness")
    #cnf += cnfPessimisticSupersetStrategyproofness()
    #print("cnfOptimisticSubsetStrategyproofness")
    #cnf += cnfOptimisticSubsetStrategyproofness()
    #print("cnfPessimisticSubsetStrategyproofness")
    #cnf += cnfPessimisticSubsetStrategyproofness()
    #print("cnfKellyCardinalityStrategyproofness")
    #cnf += cnfKellyCardinalityStrategyproofness()
    #print("cnfKelly2CardinalityStrategyproofness")
    #cnf += cnfKelly2CardinalityStrategyproofness()
    print("cnfKellySupersetStrategyproofness")
    cnf += cnfKellySupersetStrategyproofness()
    print("Solving...", file=stderr)



    # Prints how many voting rules there are according to the specifications
    # First counts up to 50, and then only shows the count every 100 found
    # Finally prints an example of a voting rule
    counter = 0    
    for sol in pylgl.itersolve(cnf):
        counter += 1
        if(counter % 100 == 0 or counter <= 50):
            print(counter)
    print(counter)
    if False:
        ans = pylgl.solve(cnf)
        a = sorted([x for x in ans if x>0])
        for i in a:
            l = int2lit[i]
            print("{} elects: {}".format(l[1], l[0]))
    else:
        print("UNSATISFIABLE")




