package hu.bme.mit.theta.common.version;

import java.io.IOException;
import java.io.InputStream;
import java.util.Properties;

public class VersionInfo {
    final static VersionInfo INSTANCE;

    public static VersionInfo getInstance() {
        return INSTANCE;
    }

    static {
        try (InputStream input = VersionInfo.class.getClassLoader().getResourceAsStream("version.properties")) {
            if (input == null) {
                throw new Error("Unable to find version.properties");
            }

            Properties properties = new Properties();
            properties.load(input);

            INSTANCE = new VersionInfo(
                properties.getProperty("name"),
                properties.getProperty("version"),
                properties.getProperty("gitBranch"),
                properties.getProperty("gitCommit")
            );

        } catch (IOException ex) {
            ex.printStackTrace();
            throw new Error(ex);
        }
    }

    private final String name;
    private final String version;
    private final String gitBranch;
    private final String gitCommit;

    public VersionInfo(final String name, final String version, final String gitBranch, final String gitCommit) {
        this.name = name;
        this.version = version;
        this.gitBranch = gitBranch;
        this.gitCommit = gitCommit;
    }

    public String getName() {
        return name;
    }

    public String getVersion() {
        return version;
    }

    public String getGitBranch() {
        return gitBranch;
    }

    public String getGitCommit() {
        return gitCommit;
    }
}
