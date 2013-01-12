import java.util.*;
import java.io.*;

public class PAFTest {
    public static void main (String[] args) throws IOException {
	Properties props = new Properties ();
	if (args.length > 0) {
	    props.load (new FileInputStream (args[0]));
	} else {
	    props.load (new FileInputStream ("paftest.txt"));
	}
	new File(props.getProperty("csvdir")).mkdirs ();
	new File(props.getProperty("dotdir")).mkdirs ();

	String mode = props.getProperty("mode").trim();
	if (mode.equals ("compare")) {
	    runCompare (props);
	} else if (mode.equals ("describe")) {
	    runDescribe (props);
	} else if (mode.equals ("generate")) {
	    Generator.generateInstance (props);
	} else if (mode.equals ("test")) {
	    runTest (props);
	}
    }

    static void runCompare (Properties props) throws IOException {
	String compare = props.getProperty ("compare");
	for (String type: compare.split(" ")) {
	    if (type.trim().length() > 0) {
		runSingleCompare (props, type);
	    }
	}
    }

    static void runSingleCompare (Properties props, String type) throws IOException {
	String prefix = "compare."+type+".";
	String csvdir = props.getProperty ("csvdir");
	String inputdir = props.getProperty ("inputdir");

	Semantics first = Semantics.fromName (props.getProperty (prefix+"first"));
	Semantics second = Semantics.fromName (props.getProperty (prefix+"second"));
	Semantics exact = Semantics.fromName (props.getProperty (prefix+"exact"));
	Montecarlo m = Montecarlo.fromString (props.getProperty (prefix+"mode"));
	Montecarlo mex = null;

	PrintWriter pw = new PrintWriter (new FileOutputStream (csvdir+"/"+type+".csv"), true);
	if (exact != null) {
	    pw.println ("Args,"+Stats.headerString("Naive ")+","+Stats.headerString("Optim ")+",Exact");
	    mex = Montecarlo.fromString (props.getProperty (prefix+"exactmode"));
	} else {
	    pw.println ("Args,"+Stats.headerString("Naive ")+","+Stats.headerString("Optim "));
	}
	for (int args=10; args <= 20; args++) {
	    Instance instance = new Instance (inputdir+"/instance"+args+".txt");
	    PAF paf = instance.paf;
	    ArgSet set = instance.set;
	    // some debug
	    System.out.println ("Args "+args);
	    System.out.println("Nodes: "+paf.args.size()+" Defeats: "+paf.defeatsList.size());
	    System.out.println("Search space: "+(Math.pow(2, paf.args.size())*Math.pow(2, paf.defeatsList.size())));
	    System.out.println("Set: "+set);
	    System.out.println("First conditional: "+first.conditional (paf, set));
	    System.out.println("Second conditional: "+second.conditional (paf, set));

	    Stats s1 = m.runs (first, paf, set, 20);
	    Stats s2 = m.runs (second, paf, set, 20);
	    double exactValue = 0;
	    if (exact != null) {
		exactValue = exact.conditional(paf, set)*mex.run (exact, paf, set).toDouble();
	    }
	    if (exact != null) {
		pw.println (args+","+s1.toString()+","+s2.toString()+","+exactValue);
	    } else {
		pw.println (args+","+s1.toString()+","+s2.toString());
	    }
	}
	pw.close ();
    }

    static void runDescribe (Properties props) throws IOException {
	String inputdir = props.getProperty ("inputdir");
	String csvdir = props.getProperty ("csvdir");
	String dotdir = props.getProperty ("dotdir");
	int from = Integer.parseInt (props.getProperty ("describe.from"));
	int to = Integer.parseInt (props.getProperty ("describe.to"));

	PrintWriter pw = new PrintWriter (new FileOutputStream (csvdir+"/instance_descriptions.csv"), true);
	pw.println ("Args,Defeats,Set size,CF,Admissible,Complete,Preferred,Grounded");
	for (int i=from; i <= to; i++) {
	    System.out.println ("Describing instance: "+i);
	    Instance pair = new Instance (inputdir+"/instance"+i+".txt");
	    PAF paf = pair.paf;
	    ArgSet set = pair.set;
	    System.out.println("Nodes: "+paf.args.size()+" Defeats: "+paf.defeatsList.size());
	    System.out.println("Search space: "+(Math.pow(2, paf.args.size())*Math.pow(2, paf.defeatsList.size())));
	    pair.writeDot (dotdir+"/instance"+i+".dot");

	    Montecarlo m = new MontecarloError (1.96, 0.005);
	    double cf = paf.conflictFree(set);
	    System.out.println ("CF: "+cf);
	    double admissible = paf.admissible(set);
	    System.out.println ("Admissible: "+admissible);
	    double complete = cf*m.run (new CompleteGivenConflictFreeSemantics(), paf, set).toDouble();
	    System.out.println ("Complete: "+complete);
	    double preferred = cf*m.run (new PreferredGivenConflictFreeSemantics(), paf, set).toDouble();
	    System.out.println ("Preferred: "+preferred);
	    double grounded = cf*m.run (new GroundedGivenConflictFreeSemantics(), paf, set).toDouble();
	    System.out.println ("Grounded: "+grounded);
	    pw.println(i+","+paf.defeatsList.size()+","+set.size()+","+cf+","+admissible+","+complete+","+preferred+","+grounded);
	}
	pw.close ();
    }

    static void runTest (Properties props) throws IOException {
	String inputdir = props.getProperty ("inputdir");
	Instance pair = new Instance (inputdir+"/test.txt");
	PAF paf = pair.paf;
	ArgSet set = pair.set;

	Montecarlo m = new MontecarloIter (100000);
	Semantics compl = new CompleteSemantics();
	System.out.println("exact cf: "+paf.depthFirst (new ConflictFreeSemantics(), set));
	double padm = paf.depthFirst (new AdmissibleSemantics(), set);
	System.out.println("exact admissible: "+padm);
	System.out.println("exact admissible (formula): "+paf.admissible (set));
	double pcomp = paf.depthFirst (compl, set);
	System.out.println("exact complete: "+pcomp);
	System.out.println("exact complete|admissible: "+(pcomp/padm));

	System.out.println("mc complete: "+m.run(compl, paf, set).toDouble());

	Semantics complGA1 = new CompleteGivenAdmissibleSemantics1();
	Semantics complGA2 = new CompleteGivenAdmissibleSemantics2();
	for (Semantics sem: new Semantics[]{complGA1, complGA2}) {
	    System.out.println ("");
	    double p = m.run(sem, paf, set).toDouble();
	    System.out.println("mc complete|admissible: "+p);
	    System.out.println("mc complete|admissible*admissible: "+sem.conditional(paf, set)*p);
	}
    }

    /*
    public static void testCorrectness () {
	PAF paf = new PAF();
	paf.addArgs ("a", 1.0,
		     "b", 2/3.0,
		     "c", 2/3.0,
		     "d", 1.0);
	paf.addDefeats ("a", "b", 2/3.0,
			"b", "c", 2/3.0);
	ArgSet s = new ArgSet ("c");
	MontecarloError m = new MontecarloError (1.96, 0.01);
	System.out.println (paf.depthFirst (new AdmissibleSemantics(), s)); // 0.37
	System.out.println (m.runs (new AdmissibleSemantics(), s, 1.96, 0.01));
        System.out.println (paf.admissible (s));
        System.out.println ();

	s = new ArgSet ("c", "d");
	System.out.println (paf.montecarlo (new AdmissibleSemantics(), s, 1.96, 0.01));
	System.out.println (paf.depthFirst (new AdmissibleSemantics(), s)); // 0.37
        System.out.println (paf.admissible (s));
        System.out.println ();

	s = new ArgSet ("a", "c", "d");
	System.out.println (paf.montecarlo (new AdmissibleSemantics(), s, 1.96, 0.01));
	System.out.println (paf.depthFirst (new AdmissibleSemantics(), s)); // 0.5679
        System.out.println (paf.admissible (s));
        System.out.println ();
    }

    public static void paperExamples () {
	PAF paf = new PAF();
	paf.addArgs ("a", 1.0,
		     "b", 1.0,
		     "c", 0.7,
		     "d", 0.3);
	paf.addDefeats ("a", "c", 1.0,
			"d", "a", 1.0);
	ArgSet s = new ArgSet ("a", "b");
	System.out.println (paf.depthFirst (new CompleteSemantics(), s)); // 0.7
	System.out.println (paf.depthFirst (new GroundedSemantics(), s)); // 0.7
    }
    */
}
