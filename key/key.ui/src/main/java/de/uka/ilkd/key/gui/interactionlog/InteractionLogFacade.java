package de.uka.ilkd.key.gui.interactionlog;

import de.uka.ilkd.key.gui.interactionlog.model.*;
import de.uka.ilkd.key.gui.interactionlog.model.builtin.*;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Marshaller;
import javax.xml.bind.Unmarshaller;
import java.io.File;

/**
 * @author Alexander Weigl
 * @version 1 (06.12.18)
 */
public final class InteractionLogFacade {
    public static JAXBContext createContext() throws JAXBException {
        JAXBContext ctx = JAXBContext.newInstance(
                InteractionLog.class,
                AutoModeInteraction.class,
                NodeInteraction.class,
                MacroInteraction.class,
                SettingChangeInteraction.class,
                UserNoteInteraction.class,
                BuiltInRuleInteraction.class,
                ContractBuiltInRuleInteraction.class,
                LoopContractInternalBuiltInRuleInteraction.class,
                MergeRuleBuiltInRuleInteraction.class,
                OSSBuiltInRuleInteraction.class,
                SMTBuiltInRuleInteraction.class,
                UseDependencyContractBuiltInRuleInteraction.class,
                PruneInteraction.class,
                RuleInteraction.class,
                NodeIdentifier.class,
                Interaction.class);
        return ctx;
    }

    /**
     * @param inputFile
     * @return
     * @throws JAXBException
     */
    public static InteractionLog readInteractionLog(File inputFile)
            throws JAXBException {
        JAXBContext ctx = createContext();
        Unmarshaller unmarshaller = ctx.createUnmarshaller();
        return (InteractionLog) unmarshaller.unmarshal(inputFile);
    }

    /**
     * @param log
     * @param output
     * @throws JAXBException
     */
    public static void storeInteractionLog(InteractionLog log, File output)
            throws JAXBException {
        JAXBContext ctx = createContext();
        Marshaller marshaller = ctx.createMarshaller();
        marshaller.setProperty(Marshaller.JAXB_FORMATTED_OUTPUT, Boolean.TRUE);
        marshaller.marshal(log, output);
    }
}
