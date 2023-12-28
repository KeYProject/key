package de.uka.ilkd.key.proof.init.loader;

import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.speclang.Contract;

/**
 * @author Alexander Weigl
 * @version 1 (28.12.23)
 */
public class FunctionalBlockContractPOLoader implements ProofObligationLoader {
    /**
     * Instantiates a new proof obligation with the given settings.
     *
     * @param initConfig The already load {@link InitConfig}.
     * @param properties The settings of the proof obligation to instantiate.
     * @return The instantiated proof obligation.
     */
    @Override
    public IPersistablePO.LoadedPOContainer loadFrom(InitConfig initConfig, Configuration properties) {
        String contractName = properties.getString("contract");
        int proofNum = 0;
        String baseContractName;
        int ind = -1;
        for (String tag : FunctionalBlockContractPO.TRANSACTION_TAGS.values()) {
            ind = contractName.indexOf("." + tag);
            if (ind > 0) {
                break;
            }
            proofNum++;
        }
        if (ind == -1) {
            baseContractName = contractName;
            proofNum = 0;
        } else {
            baseContractName = contractName.substring(0, ind);
        }
        final Contract contract = initConfig.getServices().getSpecificationRepository()
                .getContractByName(baseContractName);
        if (contract == null) {
            throw new RuntimeException("Contract not found: " + baseContractName);
        } else {
            ProofOblInput po = contract.createProofObl(initConfig);
            return new IPersistablePO.LoadedPOContainer(po, proofNum);
        }
    }

    @Override
    public boolean handles(String identifier) {
        return FunctionalBlockContractPO.class.getName().equals(identifier)
                || FunctionalBlockContractPO.class.getSimpleName().equals(identifier)
                || FunctionalBlockContractPOLoader.class.getSimpleName().equals(identifier)
                || FunctionalBlockContractPOLoader.class.getName().equals(identifier);
    }
}
