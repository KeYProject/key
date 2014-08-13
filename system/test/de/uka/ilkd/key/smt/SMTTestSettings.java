package de.uka.ilkd.key.smt;

import java.io.File;
import java.util.Collection;

import de.uka.ilkd.key.gui.configuration.PathConfig;
import de.uka.ilkd.key.gui.smt.ProofDependentSMTSettings;
import de.uka.ilkd.key.rule.Taclet;

public class SMTTestSettings implements de.uka.ilkd.key.smt.SMTSettings{


	public long getGlobalBound(){
		return 0;
	}

    @Override
    public int getMaxConcurrentProcesses() {
	return 1;
    }

    @Override
    public int getMaxNumberOfGenerics() {
	return 2;
    }

    @Override
    public String getSMTTemporaryFolder() {
	return   PathConfig.getKeyConfigDir()
	    + File.separator + "smt_formula";
    }

    @Override
    public Collection<Taclet> getTaclets() {
	return null;
    }

    @Override
    public long getTimeout() {
	return 300000;
    }

    @Override
    public boolean instantiateNullAssumption() {
	return true;
    }

    @Override
    public boolean makesUseOfTaclets() {
	return false;
    }

    @Override
    public boolean useExplicitTypeHierarchy() {
	return false;
    }
    
    @Override
    public boolean useBuiltInUniqueness() {
         return false;
    }

    @Override
    public boolean useAssumptionsForBigSmallIntegers() {
	return false;
    }

    @Override
    public boolean useUninterpretedMultiplicationIfNecessary() {
	return false;
    }

@Override
public long getMaximumInteger() {

        return ProofDependentSMTSettings.getDefaultSettingsData().maxInteger;
}

@Override
public long getMinimumInteger() {

        return ProofDependentSMTSettings.getDefaultSettingsData().minInteger;
}

@Override
public String getLogic() {
	return "AUFLIA";
}

@Override
public boolean checkForSupport() {
	return false;
}

@Override
public long getIntBound() {
	return 3;
}

@Override
public long getHeapBound() {
	return 3;
}

@Override
public long getSeqBound() {
	return 3;
}

@Override
public long getObjectBound() {
	return 3;
}

@Override
public long getLocSetBound() {
	return 3;
}

@Override
public boolean invarianForall() {
	return false;
}

    
}
