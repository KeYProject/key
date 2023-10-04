package org.keyproject.key.remoteclient;

class SimpleClient implements ClientApi {

    @Override
    public void sayHello(String e) {
        System.out.format("Hello, %s%n", e);
    }
}
