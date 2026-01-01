package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.proof.mgt.SpecificationRepository;

/**
 *
 * @author Alexander Weigl
 * @version 1 (1/1/26)
 */
public interface TacletPOGenerator {
    void generate(AbstractPO abstractPO, InitConfig initConfig, SpecificationRepository specRepo);
}
