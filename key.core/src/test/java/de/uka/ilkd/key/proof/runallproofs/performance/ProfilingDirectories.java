/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.runallproofs.performance;

import java.io.File;
import java.text.SimpleDateFormat;
import java.util.Date;

import de.uka.ilkd.key.proof.runallproofs.RunAllProofsDirectories;

import org.jspecify.annotations.NonNull;

@SuppressWarnings("serial")
public class ProfilingDirectories extends RunAllProofsDirectories {

    public final @NonNull File profilingDataDir;
    public final @NonNull File ruleIndependentDataDir;
    public final @NonNull File ruleDependentDataDir;
    public final @NonNull File computeCostDataDir;
    public final @NonNull File instantiateAppDataDir;
    private final @NonNull File runDir;

    public ProfilingDirectories(Date runStart) {
        SimpleDateFormat format = new SimpleDateFormat("dd.MMM_yyyy____HH:mm:ss");
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
