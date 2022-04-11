package de.uka.ilkd.key.proof.mgt;

import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.DependencyContractImpl;
import de.uka.ilkd.key.speclang.FunctionalOperationContractImpl;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nullable;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.Map;

public class ContractOrderManager {
    private static final Logger LOGGER = LoggerFactory.getLogger(ContractOrderManager.class);

    public static final String KEY_CONTRACT_ORDER = "key.contractOrder";
    public static final String FILENAME = System.getProperty(KEY_CONTRACT_ORDER);
    private static ContractOrderManager theInstance;

    public enum ContractMode { WITH_MEASURED_BY, UNRESTRICTED, FORBIDDEN }

    private final Map<String, Integer> map;
    private final int defaultLevel;

    private static boolean fileChecked = false;

    @Nullable
    public static ContractOrderManager tryGetInstance() {
        if(theInstance == null && !fileChecked) {
            fileChecked = true;
            if (FILENAME != null) {
                LOGGER.info("Loading contract order from " + Paths.get(FILENAME).toAbsolutePath());
                try {
                    theInstance = new ContractOrderManager();
                    LOGGER.info("Enabled contract order with " + theInstance.map.size() + " contracts");
                } catch (IOException e) {
                    LOGGER.warn("Failed to load contract order", e);
                }
            } else {
                LOGGER.warn("Contract order filename is null");
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
            System.err.println("Contract " + contract + " w/o level, using highest level");
            level = this.defaultLevel;
        }
        return level;
    }

    public ContractMode mayUse(Contract user, Contract used) {
        String nameUser = getName(user);
        if (nameUser == null) {
            System.err.println("Contract 'user' without name: " + user);
            return ContractMode.FORBIDDEN;
        }

        String nameUsed = getName(used);
        if (nameUsed == null) {
            System.err.println("Contract 'used' without name: " + used);
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
            FunctionalOperationContractImpl operationContract = (FunctionalOperationContractImpl) contract;
            return operationContract.getName();
        }

        return null;
    }

}
