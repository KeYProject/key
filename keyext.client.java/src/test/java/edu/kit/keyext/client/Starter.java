package edu.kit.keyext.client;

import edu.kit.iti.formal.keyextclientjava.KeyRemote;
import edu.kit.iti.formal.keyextclientjava.RPCLayer;
import org.junit.jupiter.api.Test;

import java.io.IOException;

import static edu.kit.iti.formal.keyextclientjava.MyKeyClient.JAR_FILE;

/**
 * @author Alexander Weigl
 * @version 1 (24.11.24)
 */
public class Starter {
    @Test
    void test() throws IOException {
        var file = "/home/weigl/work/key/keyext.api/build/libs/keyext.api-2.12.4-dev-all.jar";
        var remote = new KeyRemote(RPCLayer.startWithCLI(file));
        System.out.println(remote.meta_version());
    }
}
