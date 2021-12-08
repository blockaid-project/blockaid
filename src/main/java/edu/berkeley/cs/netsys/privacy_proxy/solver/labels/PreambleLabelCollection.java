package edu.berkeley.cs.netsys.privacy_proxy.solver.labels;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Streams;
import edu.berkeley.cs.netsys.privacy_proxy.policy_checker.Policy;
import edu.berkeley.cs.netsys.privacy_proxy.solver.Dependency;

import java.util.Collection;
import java.util.Optional;
import java.util.function.BiConsumer;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * An immutable collection of preamble labels.
 */
public class PreambleLabelCollection {
    private final String PREAMBLE_NAME_PREFIX = "PreambleLabel_";
    private final Pattern PREAMBLE_NAME_PATTERN = Pattern.compile(PREAMBLE_NAME_PREFIX + "(\\d+)_\\d+");
    private final ImmutableList<PreambleLabel> labels;

    public PreambleLabelCollection(Collection<Dependency> dependencies, Collection<Policy> policies) {
        this.labels = Streams.concat(
                dependencies.stream().map(DependencyLabel::new),
                policies.stream().map(PolicyLabel::new)
        ).collect(ImmutableList.toImmutableList());
    }

    public void forEachWithName(BiConsumer<String, PreambleLabel> function) {
        for (int i = 0; i < labels.size(); ++i) {
            function.accept(PREAMBLE_NAME_PREFIX + i, labels.get(i));
        }
    }

    public Optional<PreambleLabel> parse(String name) {
        Matcher m = PREAMBLE_NAME_PATTERN.matcher(name);
        if (!m.matches()) {
            return Optional.empty();
        }

        int i = Integer.parseInt(m.group(1));
        return Optional.of(labels.get(i));
    }
}
