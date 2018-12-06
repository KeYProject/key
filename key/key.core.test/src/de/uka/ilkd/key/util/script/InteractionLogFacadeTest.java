package de.uka.ilkd.key.util.script;

import org.junit.Assert;

import java.io.File;
import java.io.IOException;

/**
 * @author Alexander Weigl
 * @version 1 (06.12.18)
 */
public class InteractionLogFacadeTest {
    @org.junit.Test
    public void storeAndReadInteractionLogEmpty() throws IOException {
        InteractionLog il = new InteractionLog(name);
        File file = File.createTempFile("interaction_log", "xml");
        InteractionLogFacade.storeInteractionLog(il, file);
        InteractionLog readIl = InteractionLogFacade.readInteractionLog(file);
        Assert.assertEquals(0, readIl.getInteractions().size());
    }
}