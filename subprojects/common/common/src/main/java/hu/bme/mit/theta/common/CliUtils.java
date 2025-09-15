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
package hu.bme.mit.theta.common;

import java.io.PrintStream;

public class CliUtils {

    private CliUtils() {}

    public static void printVersion(PrintStream ps) {
        String ver = new CliUtils().getClass().getPackage().getImplementationVersion();
        if (ver == null) {
            ver = "Unknown version. Are you running from JAR file?";
        }
        ps.println(ver);
    }
}
