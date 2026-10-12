"""Independent exact successor rule; positive renewable-2 demands are required.
All checks use explicit exceptions and survive python -O. No solver imports.
"""

def require(condition, message):
    if not condition:
        raise ValueError(message)


def successors(t, state, modes, domains, pred, caps, horizon, idle_budget):
    """Every permitted next integer-slot state of the shared-mode relaxation.
    Bits use original job IDs. A running item is (job, source_mode, remaining).
    The returned subset is also provided for independently replayable prefixes.
    """
    done, active, idle = state
    used = done
    room, need = caps[0], caps[1]
    for j, m, remaining in active:
        used |= 1 << j
        q = modes[j][m][1]
        room -= q[0]
        need -= q[1]
    require(room >= 0 and need >= 0, 'active capacity')
    ready = [j for j in domains if not (used & (1 << j))
             and not (pred[j] & ~done)]

    def subsets(k, room_left, need_left, chosen):
        if need_left == 0:
            new_idle = idle + room_left
            if new_idle > idle_budget:
                return
            new_done, new_active = done, []
            for j, m, remaining in active + chosen:
                if remaining == 1:
                    new_done |= 1 << j
                else:
                    new_active.append((j, m, remaining - 1))
            yield ((new_done, tuple(sorted(new_active)), new_idle), chosen)
            return
        if k == len(ready):
            return
        j = ready[k]
        # Exclude j, or select exactly one of its admitted original modes.
        yield from subsets(k + 1, room_left, need_left, chosen)
        for m in domains[j]:
            d, q = modes[j][m]
            if (t + d <= horizon and q[0] <= room_left
                    and q[1] <= need_left):
                yield from subsets(k + 1, room_left - q[0],
                                   need_left - q[1], chosen + ((j, m, d),))
    yield from subsets(0, room, need, ())


def check_frontiers(frontiers, modes, domains, pred, caps, horizon, idle_budget):
    """Replay ALL successors; a stored hash or solver status is never sufficient."""
    require(frontiers[0] == {(0, (), 0)}, 'initial frontier')
    count = 0
    ambiguous = 0
    for t, (current, expected) in enumerate(zip(frontiers, frontiers[1:])):
        require(bool(current), 'premature empty frontier')
        actual = set()
        for state in current:
            for new_state, selected in successors(
                    t, state, modes, domains, pred, caps, horizon, idle_budget):
                actual.add(new_state)
                count += 1
                ambiguous += sum(len(domains[j]) > 1 for j, m, d in selected)
        require(actual == expected, 'incomplete or altered frontier at ' + str(t+1))
    require(not frontiers[-1], 'unclosed prefix')
    return count, ambiguous
