import java.io.*;

public class Instance {
    PAF paf;
    ArgSet set;

    public Instance (PAF paf, ArgSet set) {
	this.paf = paf;
	this.set = set;
    }

    public Instance (String filename) throws IOException {
	BufferedReader r = new BufferedReader (new FileReader (filename));
	paf = new PAF();
	String[] args = r.readLine ().split (" ");
	for (String a: args) {
	    if (!a.trim().equals ("")) {
		String[] entry = a.trim().split(",");
		paf.addArg (entry[0].trim(), Double.parseDouble(entry[1].trim()));
	    }
	}
	String[] defs = r.readLine ().split (" ");
	for (String d: defs) {
	    if (!d.trim().equals ("")) {
		String[] entry = d.trim().split(",");
		paf.addDefeat (entry[0].trim(), entry[1].trim(), Double.parseDouble (entry[2].trim()));
	    }
	}
	set = new ArgSet ();
	args = r.readLine().split (" ");
	for (String a: args) {
	    if (a.trim() != "") {
		set.add (a.trim());
	    }
	}
	r.close ();
    }

    void writeDot (String dotfile) throws IOException {
	PrintWriter pw = new PrintWriter (new FileOutputStream (dotfile), true);
	pw.println ("digraph {");
	for (String a: paf.argsList) {
	    if (set.contains (a)) {
		pw.println ("\t"+a+" [shape=box];");
	    }
	    pw.println ("\t"+a+" [label=\""+a+"\\n"+paf.args.get(a)+"\"];");
	    for (String b: paf.getDefeats(a).keySet()) {
		pw.println ("\t"+a+" -> "+b+" [label="+paf.defeats.get(a).get(b)+"];");
	    }
	}
	pw.println ("}");
	pw.close ();
    }

    void writeInstance (String graphfile) throws IOException {
	PrintWriter pw = new PrintWriter (new FileOutputStream (graphfile), true);
	pw.println (paf.toString ());
	pw.println (set.toString ());
	pw.close ();
    }
}
