/*
 *  Copyright 2025 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.analysis.algorithm.arg.debug;

import com.corundumstudio.socketio.Configuration;
import com.corundumstudio.socketio.SocketIOServer;
import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgEdge;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode;
import java.util.LinkedList;
import java.util.List;

/**
 * Use http://leventebajczi.com/theta-debugger/ to connect to Theta and see the ARG being built.
 * Modify the *debug* field below to true in order to enable the debugger.
 */
public final class ARGWebDebugger {
    public static boolean on = false;
    private static final Integer PORT = 8080;

    private static SocketIOServer server;
    private static final Object lock = new Object();
    private static volatile boolean received;
    private static volatile boolean waiting;

    private static final List<String> replayLog = new LinkedList<>();

    private ARGWebDebugger() {}

    private static void startServer() {
        if (!on) return;
        Configuration config = new Configuration();
        config.setPort(PORT);

        server = new SocketIOServer(config);
        server.addEventListener(
                "continue",
                String.class,
                (client, data, ackSender) -> {
                    received = true;
                    synchronized (lock) {
                        lock.notifyAll();
                    }
                });
        server.addConnectListener(
                client -> {
                    for (String s : replayLog) {
                        System.err.println("Replaying " + s);
                        client.sendEvent("message", s);
                    }
                    if (waiting) client.sendEvent("message", "{\"method\": \"wait\"}");
                });
        server.start();
        waitUntil();
    }

    private static void send(String data, boolean log) {
        if (server == null) startServer();
        if (log) replayLog.add(data);
        server.getAllClients().forEach(client -> client.sendEvent("message", data));
    }

    private static void waitUntil() {
        if (server == null) startServer();
        send("{\"method\": \"wait\"}", false);
        synchronized (lock) {
            while (!received) {
                waiting = true;
                try {
                    lock.wait(1000);
                } catch (InterruptedException e) {
                    e.printStackTrace();
                }
            }
            received = false; // Reset for the next wait
            waiting = false;
        }
    }

    private static <A extends Action> String nodeToString(
            ArgNode<? extends State, ? extends Action> node, A action) {
        return "{\"name\": \"Node "
                + node.getId()
                + "\","
                + " \"attributes\": {"
                + (action == null
                        ? ""
                        : "\"action\": \""
                                + action.toString().replaceAll("[\\n\\r\\t\"]", " ")
                                + "\",")
                + "\"state\": \""
                + node.getState().toString().replaceAll("[\\n\\r\\t\"]", " ")
                + "\""
                + ","
                + "\"target\": \""
                + node.isTarget()
                + "\""
                + "},"
                + " \"tooltip\": {"
                + (action == null
                        ? ""
                        : "\"action\": \""
                                + action.toString().replaceAll("[\\n\\r\\t\"]", " ")
                                + "\",")
                + "\"state\": \""
                + node.getState().toString().replaceAll("[\\n\\r\\t\"]", " ")
                + "\""
                + "},"
                + " \"id\": "
                + node.getId()
                + "}";
    }

    public static void create(ArgNode<? extends State, ? extends Action> initNode) {
        if (!on) {
            return;
        }
        replayLog.clear();
        send("{\"method\": \"create\", \"node\": " + nodeToString(initNode, null) + "}", true);
        waitUntil();
    }

    public static <A extends Action> void add(
            ArgNode<? extends State, ? extends Action> parent,
            A action,
            ArgNode<? extends State, ? extends Action> child) {
        if (!on) {
            return;
        }
        send(
                "{\"method\": \"add\", \"parent\": "
                        + parent.getId()
                        + ", \"child\": "
                        + nodeToString(child, action)
                        + "}",
                true);
        waitUntil();
    }

    public static <A extends Action> void remove(ArgEdge<? extends State, ? extends Action> edge) {
        if (!on) {
            return;
        }
        send(
                "{\"method\": \"delete\", \"parent\": "
                        + edge.getSource().getId()
                        + ", \"child\": "
                        + edge.getTarget().getId()
                        + "}",
                true);
        waitUntil();
    }
}
