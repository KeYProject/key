/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.proof.mgt;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.DependencyContractImpl;
import de.uka.ilkd.key.speclang.FunctionalOperationContractImpl;

public class ContractOrderManager {
    public static final String KEY_CONTRACT_ORDER = "key.contractOrder";
    public static final String FILENAME = System.getProperty(KEY_CONTRACT_ORDER);
    private static ContractOrderManager theInstance;

    public enum ContractMode {
        WITH_MEASURED_BY, UNRESTRICTED, FORBIDDEN
    }

    private final Map<String, Integer> map;
    private final int defaultLevel;

    public static boolean isEnabled() {
        return FILENAME != null;
    }

    public static ContractOrderManager getInstance() {
        assert isEnabled();
        if (theInstance == null) {
            try {
                theInstance = new ContractOrderManager();
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
        return theInstance;
    }

    private ContractOrderManager() throws IOException {
        int level = 0;
        Map<String, Integer> result = new HashMap<>();
        for (String line : Files.readAllLines(Paths.get(FILENAME))) {
            if (line.startsWith("#")) {
                continue;
            }
            if (line.isEmpty()) {
                level++;
            } else {
                result.put(line, level);
            }
        }
        this.map = result;
        this.defaultLevel = level + 1;
    }

    private int getLevel(String contract) {
        // Could be replaced by getOrDefault, keeping the debug output for now
        Integer level = map.get(contract);
        if (level == null) {
            // System.out.println("Contract " + contract + " w/o level, using highest level");
            level = this.defaultLevel;
        }
        return level;
    }

    public ContractMode mayUse(Contract user, Contract used) {
        String nameUser = getName(user);
        if (nameUser == null) {
            System.out.println("Contract 'user' without name: " + user);
            return ContractMode.FORBIDDEN;
        }

        String nameUsed = getName(used);
        if (nameUsed == null) {
            System.out.println("Contract 'used' without name: " + used);
            return ContractMode.FORBIDDEN;
        }

        int levelUser = getLevel(nameUser);
        int levelUsed = getLevel(nameUsed);

        if (levelUser > levelUsed) {
            return ContractMode.UNRESTRICTED;
        }

        return ContractMode.WITH_MEASURED_BY;
    }

    private static String getName(Contract contract) {
        if (contract instanceof DependencyContractImpl) {
            DependencyContractImpl dependencyContract = (DependencyContractImpl) contract;
            return dependencyContract.getName();
        }

        if (contract instanceof FunctionalOperationContractImpl) {
            FunctionalOperationContractImpl operationContract =
                (FunctionalOperationContractImpl) contract;
            return operationContract.getName();
        }

        return null;
    }

}
