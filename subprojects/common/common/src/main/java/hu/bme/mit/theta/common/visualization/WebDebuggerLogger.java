/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.common.visualization.writer;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.ArrayList;

// TODO refactor and enhance this class and related features?
public class WebDebuggerLogger {
    private static final WebDebuggerLogger instance = new WebDebuggerLogger();
    private static Boolean enabled = false;

    private final ArrayList<String> iterations = new ArrayList<String>();
    private final ArrayList<String> traces = new ArrayList<String>();
    private String title = "Cfa";

    private WebDebuggerLogger() {
    }

    public static void enableWebDebuggerLogger() {
        enabled = true;
    }

    public static WebDebuggerLogger getInstance() {
        return instance;
    }

    public void addIteration(int iteration, String arg, String prec) {
        if (enabled) {
            StringBuilder sb = new StringBuilder();
            sb.append("{").append(System.lineSeparator()).append("\"iteration\": ").append(iteration).append(",");
            sb.append("\"arg\": ").append(arg).append(",");
            sb.append("\"precision\": \"").append(prec).append("\"");
            sb.append("}");
            iterations.add(sb.toString());
        }
    }

    public void setTitle(String title) {
        this.title = title;
    }

    private String getFileContent() {
        StringBuilder sb = new StringBuilder();
        sb.append("{").append(System.lineSeparator());
        sb.append("\"title\": \"").append(title).append("\",").append(System.lineSeparator());
        sb.append("\"date\": \"").append(java.time.LocalDateTime.now()).append("\",").append(System.lineSeparator());
        sb.append("\"iterations\": [");
        for (String iteration : iterations) {
            sb.append(iteration).append(",");
        }
        sb.deleteCharAt(sb.length() - 1);
        sb.append("],").append(System.lineSeparator());
        sb.append("\"traces\": [");
        for (String trace : traces) {
            sb.append("\"").append(trace).append("\"").append(",\n");
        }
        sb.deleteCharAt(sb.length() - 1);
        sb.append("]").append(System.lineSeparator());
        sb.append("}");
        return sb.toString();
    }

    public void writeToFile(String fileName) {
        if (enabled) {
            String content = getFileContent();

            final File file = new File(fileName);
            try (PrintWriter printWriter = new PrintWriter(file)) {
                printWriter.write(content);
            } catch (final FileNotFoundException e) {
                System.out.println("File not found");
            }
        }
    }
}
