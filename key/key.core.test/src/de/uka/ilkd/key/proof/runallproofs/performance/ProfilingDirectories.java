package de.uka.ilkd.key.proof.runallproofs.performance;

import java.io.File;
import java.util.Date;

import de.uka.ilkd.key.proof.runallproofs.RunAllProofsDirectories;
import java.text.SimpleDateFormat;

@SuppressWarnings("serial")
public class ProfilingDirectories extends RunAllProofsDirectories {

    public final File profilingDataDir;
    public final File ruleIndependentDataDir;
    public final File ruleDependentDataDir;
    public final File computeCostDataDir;
    public final File instantiateAppDataDir;
    private final File runDir;

    public ProfilingDirectories(Date runStart) {
        super(runStart);

        SimpleDateFormat format = new SimpleDateFormat(
                "dd.MMM_yyyy____HH:mm:ss");
        String date = format.format(runStart);
        runDir = new File(RUNALLPROOFS_DIR, "run-" + date);

        profilingDataDir = new File(runDir, "profilingData");
        ruleIndependentDataDir = new File(profilingDataDir, "ruleIndependentData");
        ruleIndependentDataDir.mkdirs();
        ruleDependentDataDir = new File(profilingDataDir, "ruleDependentData");
        computeCostDataDir = new File(ruleDependentDataDir, "computeCost");
        computeCostDataDir.mkdirs();
        instantiateAppDataDir = new File(ruleDependentDataDir, "instantiateApp");
        instantiateAppDataDir.mkdirs();
    }

}
