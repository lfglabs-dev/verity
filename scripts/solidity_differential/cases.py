"""Independent ABI/storage fixture construction from solc metadata."""
import random

MODULUS = 1 << 256


def keccak(data):
    from eth_hash.auto import keccak as hash_bytes
    return hash_bytes(data)



def canonical(abi):
    return "(" + ",".join(map(canonical, abi["components"])) + ")" + abi["type"][5:] if abi["type"].startswith("tuple") else abi["type"]


def abi_value(abi, path, arguments, noise=b""):
    ty = abi["type"]
    salt = keccak(noise + path.encode()) if noise else bytes(32)
    if ty.endswith("]"):
        base, length = ty.rsplit("[", 1)
        length = length[:-1]
        return [abi_value({**abi, "type": base}, path + f"[{i}]", arguments, noise) for i in range(int(length) if length else salt[0] % 3)]
    if ty == "tuple":
        return tuple(abi_value(child, path + "." + child["name"], arguments, noise) for child in abi["components"])
    bits = 160 if ty == "address" else (1 if ty == "bool" else int(ty[4:] or 256) if ty.startswith("uint") else int(ty[3:] or 256) if ty.startswith("int") else int(ty[5:]) * 8 if ty.startswith("bytes") and ty != "bytes" else 256)
    n = arguments.get(path, int.from_bytes(salt, "big") % (1 << bits))
    if ty.startswith("int") and path not in arguments and n >= 1 << (bits - 1):
        n -= 1 << bits
    if ty == "address":
        return n.to_bytes(20, "big")
    if ty.startswith("bytes"):
        return n.to_bytes(int(ty[5:]), "big") if ty != "bytes" else salt[:salt[0] % 3]
    if ty == "string":
        return salt[:salt[0] % 3].hex()
    if ty == "bool":
        if n not in (0, 1):
            raise ValueError("invalid boolean fixture")
        return bool(n)
    return n


def mapping_slot(base, key):
    return int.from_bytes(keccak(key.to_bytes(32, "big") + base.to_bytes(32, "big")), "big")


def storage_words(layout, recipes, values):
    result = {}
    for recipe in recipes:
        field = next(f for f in layout["storage"] if f["label"] == recipe["field"])
        slot, type_id = int(field["slot"]), field["type"]
        for name in recipe["keys"]:
            ty = layout["types"][type_id]
            if ty["encoding"] != "mapping":
                raise ValueError("storage recipe key count exceeds mapping depth")
            slot = mapping_slot(slot, values[name])
            type_id = ty["value"]
        members = layout["types"][type_id]["members"]
        for member, name in recipe["members"].items():
            item = next(m for m in members if m["label"] == member)
            ty = layout["types"][item["type"]]
            if not ty["label"].startswith("uint"):
                raise ValueError("only unsigned packed storage fixtures are supported")
            width = int(ty["numberOfBytes"]) * 8
            value = values[name]
            if not 0 <= value < 1 << width:
                raise ValueError(f"out of range storage value {member}")
            address = (slot + int(item["slot"])) % MODULUS
            shift = int(item["offset"]) * 8
            mask = ((1 << width) - 1) << shift
            # Fill unused packed members with noise, not assumed zeros.
            old = result.get(address, int.from_bytes(keccak(address.to_bytes(32, "big")), "big"))
            result[address] = (old & ~mask) | (value << shift)
    return result


def materialize(config, metadata, abi, layout, values, name):
    from eth_abi import encode
    arguments = {path: values[var] for path, var in config["arguments"].items()}
    model_args = []
    projected = {p["modelParam"]: p["parameter"] + "." + p["member"] for p in metadata["projections"]}
    for param in metadata["params"]:
        model_args.append(arguments[projected.get(param, param)])
    signature = abi["name"] + "(" + ",".join(map(canonical, abi["inputs"])) + ")"
    source_data = keccak(signature.encode())[:4] + encode(
        [canonical(x) for x in abi["inputs"]], [abi_value(x, x["name"], arguments, name.encode()) for x in abi["inputs"]])
    compiled_data = bytes.fromhex("12345678") + b"".join(n.to_bytes(32, "big") for n in model_args)
    storage = storage_words(layout, config.get("storage", []), values)
    # Adjacent slots and unrelated words detect offsets / accidental reads.
    for slot in list(storage):
        for neighbor in ((slot - 1) % MODULUS, (slot + 1) % MODULUS):
            storage.setdefault(neighbor, int.from_bytes(keccak(neighbor.to_bytes(32, "big")), "big"))
    for slot in range(4):
        storage.setdefault(slot, MODULUS - slot - 1)
    observed = sorted(storage)
    return {"id": name, "args": list(map(str, model_args)), "timestamp": str(values.get(config.get("timestamp", ""), 0)),
            "storage": [[str(k), str(v)] for k, v in sorted(storage.items())], "observe": list(map(str, observed)),
            "storageCount": len(storage), "observeCount": len(observed),
            "sourceCalldata": "0x" + source_data.hex(), "compiledCalldata": "0x" + compiled_data.hex()}


def generate(config, count, seed, corpus):
    rng = random.Random(seed)
    domains = config["variables"]
    seeds = [{key: int(row.get(key, config.get("defaults", {}).get(key, 0))) for key in domains} for row in corpus] or [{key: 0 for key in domains}]
    result = [(row.get("name", f"corpus-{i}"), values) for i, (row, values) in enumerate(zip(corpus, seeds))]
    for i in range(count):
        values = dict(seeds[i % len(seeds)]) if i % 3 else {}
        for key, bits in domains.items():
            edge = [0, 1, 2, (1 << bits) - 1, (1 << bits) - 2, 1 << (bits - 1)]
            if key not in values or rng.randrange(3) == 0:
                values[key] = rng.choice(edge) if rng.randrange(2) else rng.getrandbits(bits)
        if i % 2 == 0:
            for low, high in config.get("ordered_pairs", []):
                values[low], values[high] = sorted((values[low], values[high]))
        result.append((f"seed-{seed}-{i}", values))
    return result
