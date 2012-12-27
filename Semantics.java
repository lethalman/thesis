abstract class Semantics {
    public abstract boolean evaluate (DAF daf, ArgSet set);

    public DAF montecarloSample (PAF paf, ArgSet set) {
        DAF daf;
        do {
            daf = new DAF();
	    for (String a: paf.argsList) {
		if (paf.args.get(a) >= Math.random()) {
		    daf.addArg (a);
		}
	    }
            for (String a: daf.args) {
		for (String b: paf.getDefeats(a).keySet()) {
		    if (daf.args.contains (b) && paf.defeats.get(a).get(b) >= Math.random ()) {
			daf.addDefeat (a, b);
		    }
                }
            }
        } while (filterSample (daf, set));
        return daf;
    }

    public boolean filterSample (DAF daf, ArgSet set) {
        return false; // don't filter by default
    }

    public double conditional (PAF paf, ArgSet set) {
	return 1;
    }

    public static Semantics fromName (String name) {
	if (name.equals ("null")) {
	    return null;
	}
	try {
	    return (Semantics) Class.forName(name).newInstance ();
	} catch (Exception e) {
	    throw new RuntimeException (e);
	}
    }
}


class ConflictFreeSemantics extends Semantics {
    @Override
    public boolean evaluate (DAF daf, ArgSet set) {
	return daf.conflictFree (set);
    }
}

class AdmissibleSemantics extends Semantics {
    @Override
    public boolean evaluate (DAF daf, ArgSet set) {
	return daf.admissible (set);
    }
}

class StableSemantics extends Semantics {
    @Override
    public boolean evaluate (DAF daf, ArgSet set) {
	return daf.stable (set);
    }
}

class CompleteSemantics extends Semantics {
    @Override
    public boolean evaluate (DAF daf, ArgSet set) {
	return daf.complete (set);
    }
}

class PreferredSemantics extends Semantics {
    @Override
    public boolean evaluate (DAF daf, ArgSet set) {
	return daf.preferred (set);
    }
}

class GroundedSemantics extends Semantics {
    @Override
    public boolean evaluate (DAF daf, ArgSet set) {
	return daf.grounded (set);
    }
}

abstract class GivenConflictFreeSemantics extends Semantics {
    @Override
    public DAF montecarloSample (PAF paf, ArgSet set) {
        DAF daf;
	do {
	    daf = new DAF();
	    for (String a: set) {
		// args must be in daf for set to be conflict-free
		daf.addArg (a);
	    }
	    for (String a: paf.argsList) {
                double r = Math.random();
		if (!set.contains(a) && paf.args.get(a) >= r) {
		    daf.addArg (a);
		}
	    }
	    for (String a: daf.args) {
		for (String b: paf.getDefeats(a).keySet()) {
		    if (set.contains(a) && set.contains(b)) {
			// conflict
			continue;
		    }
		    if (daf.args.contains (b) && paf.defeats.get(a).get(b) >= Math.random ()) {
			daf.addDefeat (a, b);
		    }
		}
	    }
	} while (filterSample (daf, set));
        return daf;
    }

    @Override
    public double conditional (PAF paf, ArgSet set) {
	return paf.conflictFree (set);
    }
}

abstract class GivenAdmissibleSemantics1 extends Semantics {
    @Override
    public DAF montecarloSample (PAF paf, ArgSet set) {
        DAF daf;
	do {
	    daf = new DAF();
	    for (String a: set) {
		// args must be in daf for set to be admissible
		daf.addArg (a);
	    }
	    for (String a: paf.argsList) {
		if (!set.contains(a) && Math.random () <= paf.args.get(a)) {
		    daf.addArg (a);
		}
	    }
	    for (String a: daf.args) {
		for (String b: paf.getDefeats(a).keySet()) {
		    if (set.contains(a) && set.contains(b)) {
			// conflict
			continue;
		    }
		    if (set.contains (b)) {
			// can't be handled here because it would be incorrect, do it later
			continue;
		    }
		    if (daf.args.contains (b) && Math.random () <= paf.defeats.get(a).get(b)) {
			daf.addDefeat (a, b);
		    }
		}
	    }
	    for (String a: set) {
		for (String b: paf.getDefeatedBy(a).keySet()) {
		    if (daf.args.contains (b) && !set.contains (b)) {
			// "a" must be defended from "b"
			boolean defended = false;
			for (String c: daf.getDefeatedBy(b)) {
			    if (set.contains (c)) {
				defended = true;
				break;
			    }
			}
			if (!defended) {
			    // not acceptable
			    continue;
			}
			if (Math.random() <= paf.defeats.get(b).get(a)) {
			    daf.addDefeat (b, a);
			}
		    }
		}
	    }
	} while (filterSample (daf, set));
        return daf;
    }

    @Override
    public double conditional (PAF paf, ArgSet set) {
	return paf.admissible (set);
    }
}

abstract class GivenAdmissibleSemantics extends Semantics {
    @Override
    public DAF montecarloSample (PAF paf, ArgSet set) {
        DAF daf;
	do {
	    daf = new DAF();
	    for (String a: set) {
		// args must be in daf for set to be admissible
		daf.addArg (a);
	    }
	    for (String a: paf.argsList) {
		if (!set.contains(a) && Math.random () <= paf.args.get(a)) {
		    daf.addArg (a);
		}
	    }
	    // first generate defeats toward S
	    for (String a: set) {
		for (String b: paf.getDefeatedBy(a).keySet()) {
		    if (set.contains (b)) {
			// conflict
			continue;
		    }
		    if (daf.args.contains (b) && Math.random() <= paf.defeats.get(b).get(a)) {
			// generate one defender
			boolean hasDefender = false;
			for (String c: paf.getDefeatedBy(b).keySet()) {
			    if (set.contains (c)) {
				daf.addDefeat (c, b);
				hasDefender = true;
			    }
			}
			if (hasDefender) {
			    daf.addDefeat (b, a);
			}
		    }
		}
	    }
	    // generate everything else
	    for (String a: daf.args) {
		for (String b: paf.getDefeats(a).keySet()) {
		    if (set.contains (a) || set.contains (b)) {
			// already considered
			continue;
		    }
		    if (daf.args.contains (b) && !daf.getDefeats(a).contains(b) && Math.random () <= paf.defeats.get(a).get(b)) {
			daf.addDefeat (a, b);
		    }
		}
	    }
	} while (filterSample (daf, set));
        return daf;
    }

    @Override
    public double conditional (PAF paf, ArgSet set) {
	return paf.admissible (set);
    }
}

class CompleteGivenConflictFreeSemantics extends GivenConflictFreeSemantics {
    @Override
    public boolean evaluate (DAF daf, ArgSet set) {
	return daf.completeGivenConflictFree (set);
    }
}

class CompleteGivenAdmissibleSemantics extends GivenAdmissibleSemantics {
    @Override
    public boolean evaluate (DAF daf, ArgSet set) {
	return daf.completeGivenAdmissible (set);
    }
}


class PreferredGivenConflictFreeSemantics extends GivenConflictFreeSemantics {
    @Override
    public boolean evaluate (DAF daf, ArgSet set) {
	return daf.preferredGivenConflictFree (set);
    }
}

class PreferredGivenAdmissibleSemantics extends GivenAdmissibleSemantics {
    @Override
    public boolean evaluate (DAF daf, ArgSet set) {
	return daf.preferredGivenAdmissible (set);
    }
}

class GroundedGivenConflictFreeSemantics extends GivenConflictFreeSemantics {
    @Override
    public boolean evaluate (DAF daf, ArgSet set) {
	return daf.groundedGivenConflictFree (set);
    }
}

class GroundedGivenAdmissibleSemantics extends GivenAdmissibleSemantics {
    @Override
    public boolean evaluate (DAF daf, ArgSet set) {
	return daf.groundedGivenAdmissible (set);
    }
}
