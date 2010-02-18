// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.mgt;

import java.util.*;

import javax.swing.JOptionPane;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.notification.events.GeneralFailureEvent;
import de.uka.ilkd.key.proof.JavaModel;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.reuse.ReuseFrontend;

public class GlobalProofMgt {

    private static final GlobalProofMgt INSTANCE = new GlobalProofMgt();

    private Map<EnvKey, List<ProofEnvironment>> envKeyToEnv = 
        new HashMap<EnvKey, List<ProofEnvironment>>();

    private KeYMediator mediator;

    private Logger mgtLogger = Logger.getLogger("key.proof.mgt");

    public static GlobalProofMgt getInstance() {
	return INSTANCE;
    }

    public void setMediator(KeYMediator m) {
	mediator = m;
    }

    public ProofEnvironment getProofEnvironment(JavaModel jmodel, 
						RuleConfig ruleConfig) {
	if (jmodel==null) {
	    return null;
	}
        List<ProofEnvironment> setOfEnv 
	    = envKeyToEnv.get(new EnvKey(jmodel, ruleConfig));        
	if (setOfEnv==null || setOfEnv.size()==0) {
	    return null;
	} else {
	    return setOfEnv.iterator().next();
	}
//	} else {
//	    Object[] choice = new Object[setOfEnv.size()+1];
//	    System.arraycopy(setOfEnv.toArray(), 0, choice, 1, setOfEnv.size());
//	    choice[0] = "Open in new environment";
//	    Object o =(JOptionPane.showInputDialog
//		       (mediator.mainFrame(), 
//			"Java model and rule sets are suitable "
//			+"to already existing environment(s). \n"
//			+"Please select one or choose to open the problem "
//			+"in a new environment.\n"
//			+"Attention: Unless you open the problem in a "
//			+"new environment,\n"
//			+"sort, function, and rule declarations are ignored.", 
//			"Proof Environment",
//			JOptionPane.QUESTION_MESSAGE, null, 
//			choice, null));	
//	    if (o instanceof ProofEnvironment) {
//		return (ProofEnvironment)o;
//	    } else {
//		return null;
//	    }
//	}
    }

    public void registerProofEnvironment(ProofEnvironment env) {
	EnvKey envKey = new EnvKey(env.getJavaModel(), 
				   env.getRuleConfig());
	List<ProofEnvironment> listOfEnv = envKeyToEnv.get(envKey);
	if (listOfEnv==null) {
	    listOfEnv = new LinkedList<ProofEnvironment>();
	    envKeyToEnv.put(envKey, listOfEnv);
	}
	if (!listOfEnv.contains(env)) {
	    listOfEnv.add(env);
	    env.setNumber(listOfEnv.size());
	}
    }

    public void tryReuse(ProofAggregate plist) {
        int size = plist.size();
	for (int i=0; i<size; i++) {
	    tryReuse(plist.getProofs()[i]);
	}
    }

    public void tryReuse(Proof proof) {
        Proof[] prevs = lookupPrevious(proof);
        if (prevs.length>0 && !Main.testStandalone) {
	    String[] prevNames = new String[prevs.length];
	    for (int i=0; i<prevNames.length; i++) {
		prevNames[i]="From "+prevs[i].env().description();
	    }
	    String pname = (String) JOptionPane.showInputDialog
		(mediator.mainFrame(), "Found previous proofs for this PO in "
		 +proof.env().description()+"\n"
		 +"Mark up for re-use? (previous marks will be lost)",
		 "Re-Use", JOptionPane.QUESTION_MESSAGE, null, prevNames, null);
	    
	    if (pname!=null) {
		int i=0;
		while (!pname.equals(prevNames[i])) i++;
		tryReuse(proof, prevs[i]);
	    }
        }
    }

    public void tryReuse(Proof proof, Proof prev) {
        String error = null;	
	CvsRunner cvs = new CvsRunner();
	String diff;
	Node.clearReuseCandidates();
	ReuseFrontend f = new ReuseFrontend(mediator);
	if (!proof.getJavaModel().isEmpty()) {
	    try{
		diff = cvs.cvsDiff(proof.getJavaModel().getCVSModule(), //XXX: check equality
				   prev.getJavaModel().getModelTag(), 
				   proof.getJavaModel().getModelTag());
		error = f.markup(prev, diff);
	    } catch(CvsException cvse) {
		mgtLogger.error("Diffing models in CVS failed: "+cvse);
	    }
	} else f.markRoot(prev);
	
	if (error != null) {
	    mediator.notify(new GeneralFailureEvent(error));
	}
    }
    

    private Proof[] lookupPrevious(Proof p) {
	List<Proof> result = new LinkedList<Proof>();
        for (List<ProofEnvironment> proofEnvironments : envKeyToEnv.values()) {
            List<ProofEnvironment> envList = proofEnvironments;
            for (ProofEnvironment anEnvList : envList) {
                ProofEnvironment env = anEnvList;
                for (ProofAggregate proofAggregate : env.getProofs()) {
                    ProofAggregate pl = proofAggregate;
                    Proof[] proofs = pl.getProofs();
                    for (Proof proof : proofs) {
                        if (p != proof
                                && p.mgt().proofSimilarTo(proof)) {
                            result.add(proof);
                        }
                    }
                }
            }
        }
	return result.toArray(new Proof[result.size()]);
    }
    
    
    public void removeEnv(ProofEnvironment env) {
        Set<Map.Entry<EnvKey,List<ProofEnvironment>>> entries = envKeyToEnv.entrySet();
        for (Map.Entry<EnvKey, List<ProofEnvironment>> entry1 : entries) {
            Map.Entry<EnvKey, List<ProofEnvironment>> entry = entry1;
            List<ProofEnvironment> l = entry.getValue();
            Iterator<ProofEnvironment> listIt = l.iterator();
            while (listIt.hasNext()) {
                if (listIt.next().equals(env)) listIt.remove();
            }
        }
    }

    static class EnvKey {
        private JavaModel jModel;
	private RuleConfig ruleConfig;
	private int number;

	public EnvKey (JavaModel jModel, RuleConfig ruleConfig, int number) {
	    this.jModel = jModel;
	    this.ruleConfig = ruleConfig;
	    this.number = number;
	}

	public EnvKey (JavaModel jModel, RuleConfig ruleConfig) {
	    this(jModel, ruleConfig, 0);
	}

	public JavaModel getJavaModel() {
	    return jModel;
	}

	public RuleConfig getRuleConfig() {
	    return ruleConfig;
	}

	public int getNumber() {
	    return number;
	}

	public boolean equals(Object o) {
	    if (!(o instanceof EnvKey)) return false;
	    EnvKey e = (EnvKey) o;
	    return e.getJavaModel().equals(getJavaModel()) 
		&& e.getRuleConfig().equals(getRuleConfig());
	}

	public int hashCode() {
	    int result=17;
 	    result = 37*result +getJavaModel().hashCode();
 	    result = 37*result +getRuleConfig().hashCode();
	    return result;
	}
    }

}
