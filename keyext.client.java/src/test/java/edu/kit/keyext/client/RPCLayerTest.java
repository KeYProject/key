/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package edu.kit.keyext.client;

import java.io.IOException;
import java.io.StringReader;
import java.io.StringWriter;
import java.util.concurrent.ArrayBlockingQueue;

import edu.kit.iti.formal.keyextclientjava.rpc.JsonRPC;
import edu.kit.iti.formal.keyextclientjava.rpc.RPCLayer;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

/**
 * @author Alexander Weigl
 * @version 1 (24.11.24)
 */
public class RPCLayerTest {
    @Test
    void testSending() throws IOException {
        var incoming = new StringReader("");
        var outgoing = new StringWriter();
        RPCLayer layer = new RPCLayer(incoming, outgoing);
        layer.callAsync("doSomething", 1, 1);

        var request = JsonRPC.createRequest("0", "doSomething", 1, 1);
        var requestWH = JsonRPC.addHeader(request);
        Assertions.assertEquals(requestWH, outgoing.toString());
    }

    @Test
    void testIncoming() throws IOException {
        var notification = JsonRPC.createNotification("test", 1, 2, 3, 4);
        var response = JsonRPC.createResponse("1", 2);
        final var incoming = new StringReader(JsonRPC.addHeader(notification) +
                JsonRPC.addHeader(response));
        RPCLayer.JsonStreamListener listener =
            new RPCLayer.JsonStreamListener(incoming, new ArrayBlockingQueue<>(1));
        String first = listener.readMessage();
        Assertions.assertEquals(notification, first);
        String second = listener.readMessage();
        Assertions.assertEquals(response, second);
    }



    @Test
    void testLockingAndReleasing() throws IOException, InterruptedException {
        var response = JsonRPC.addHeader(JsonRPC.createResponse("0", 2));
        var layer = new RPCLayer(new StringReader(response), new StringWriter());
        layer.start(); // starts the thread.
        var result = layer.callSync("calc", 1, 1);
        System.out.println(result);
    }
}
