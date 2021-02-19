package hu.bme.mit.theta.common;

import java.util.Arrays;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

public class SemVer implements Comparable<SemVer> {
    private final int[] version;

    private SemVer(final String version) {
        checkNotNull(version);
        checkArgument(version.matches("[0-9]+(\\.[0-9]+)*"));

        this.version = Arrays.stream(version.split("\\.")).mapToInt(Integer::parseInt).toArray();
    }

    public static SemVer of(final String version) {
        return new SemVer(version);
    }

    public boolean hasMajor() {
        return version.length > 0;
    }

    public int getMajor() {
        return version[0];
    }

    public boolean hasMinor() {
        return version.length > 1;
    }

    public int getMinor() {
        return version[1];
    }

    public boolean hasPatch() {
        return version.length > 2;
    }

    public int getPatch() {
        return version[2];
    }

    public int[] getAll() {
        return version;
    }

    @Override
    public int compareTo(final SemVer that) {
        if(that == null) {
            return 1;
        }

        for(int i = 0; i < Math.max(this.version.length, that.version.length); i++) {
            final var thisVer = i < this.version.length ? this.version[i] : 0;
            final var thatVer = i < that.version.length ? that.version[i] : 0;

            if(thisVer < thatVer) {
                return -1;
            }
            else if(thisVer > thatVer) {
                return 1;
            }
            else {
                continue;
            }
        }

        return 0;
    }

    @Override
    public boolean equals(Object obj) {
        if(obj == null) {
            return false;
        }
        else if(obj instanceof SemVer) {
            return this.compareTo((SemVer) obj) == 0;
        }
        else {
            return false;
        }
    }
}
