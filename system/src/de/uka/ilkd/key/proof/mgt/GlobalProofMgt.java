// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.proof.mgt;

import java.util.*;

import de.uka.ilkd.key.proof.*;

public final class GlobalProofMgt {

    private static final GlobalProofMgt INSTANCE = new GlobalProofMgt();

    private Map<EnvKey, List<ProofEnvironment>> envKeyToEnv = 
        new HashMap<EnvKey, List<ProofEnvironment>>();

    public static GlobalProofMgt getInstance() {
	return INSTANCE;
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

    
    public void removeEnv(ProofEnvironment env) {
        Set<Map.Entry<EnvKey,List<ProofEnvironment>>> entries = envKeyToEnv.entrySet();
        Iterator<Map.Entry<EnvKey,List<ProofEnvironment>>> it = entries.iterator();
        while (it.hasNext()) {
            Map.Entry<EnvKey,List<ProofEnvironment>> entry = it.next();
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
