package de.uka.ilkd.key.bugdetection;

import de.uka.ilkd.key.proof.Node;

public class BugDetector {

    public void run(Node n){
	FalsifiabilityPreservation fp = new FalsifiabilityPreservation();
	fp.collectFPConditions(n);
    }
}
