package de.uka.ilkd.key.proof.mgt;

import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.DependencyContractImpl;
import de.uka.ilkd.key.speclang.FunctionalOperationContractImpl;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.Map;

public class ContractOrderManager {
    public static final String KEY_CONTRACT_ORDER = "key.contractOrder";
    public static final String FILENAME = System.getProperty(KEY_CONTRACT_ORDER);
    private static ContractOrderManager theInstance;

    public enum ContractMode { WITH_MEASURED_BY, UNRESTRICTED, FORBIDDEN }

    private final Map<String, Integer> map;

    public static boolean isEnabled() {
        return FILENAME != null;
    }

    public static ContractOrderManager getInstance() {
        assert isEnabled();
        if(theInstance == null) {
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
            if (line.isEmpty()) {
                level++;
            } else {
                result.put(line, level);
            }
        }
        this.map = result;
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

        Integer levelUser = map.get(nameUser);
        if (levelUser == null) {
            System.out.println("Contract " + nameUser + " w/o level");
            return ContractMode.FORBIDDEN;
        }
        Integer levelUsed = map.get(nameUsed);
        if (levelUsed == null) {
            System.out.println("Contract " + nameUsed + " w/o level");
            return ContractMode.FORBIDDEN;
        }

        if (levelUser < levelUsed) {
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
