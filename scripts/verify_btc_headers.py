import argparse
import hashlib

MAX_TARGET_BYTES = bytes([0xff, 0xff, 0x00, 0x1d])

def sha256d(x):
    s = lambda y: hashlib.sha256(y)
    return s(s(x).digest()).digest()

def nbits_to_target(nbits: bytes) -> int:
    assert(len(nbits) == 4)
    exponent = nbits[3]
    mantissa = int.from_bytes(nbits[:3], "little")
    return mantissa * 256 ** (exponent - 3)

def target_to_nbits(value: int) -> bytes:
    exponent = 0
    while value > 256 ** 3 or value % 256 == 0:
        value //= 256
        exponent += 1
    if value & 0x800000 == 0x800000: # MSB cannot be 1 for non-negative integers
        value //= 256
        exponent += 1
    return value.to_bytes(3, "little") + (exponent + 3).to_bytes(1, "little")

def parse_timestamp(hdr: bytes) -> int:
    assert(len(hdr) == 80)
    return int.from_bytes(hdr[68:72], 'little')

def verify_pow(hdr: bytes) -> bytes:
    assert(len(hdr) == 80)
    hdr_hash = sha256d(hdr)
    hdr_hash_int = int.from_bytes(hdr_hash, 'little')
    # hdr_hash_be = hdr_hash_int.to_bytes(32, 'big')
    target = nbits_to_target(hdr[72:76])
    assert(hdr_hash_int <= target)
    return hdr_hash
    
def verify_target_update(hdr: bytes, height_mod_2016: int, prev_block_target: int, prev_block_timestamp: int, epoch_start_timestamp: int):
    current_target = nbits_to_target(hdr[72:76])
    if height_mod_2016 == 2016:
        time_diff = prev_block_timestamp - epoch_start_timestamp
        ideal_timespan = 2016 * 10 * 60

        if time_diff < ideal_timespan // 4:
            time_diff = ideal_timespan // 4
        elif time_diff > 4 * ideal_timespan:
            time_diff = 4 * ideal_timespan

        new_target = (prev_block_target * time_diff) // ideal_timespan
        max_target = nbits_to_target(MAX_TARGET_BYTES)
        if new_target > max_target:
            new_target = max_target
        assert(target_to_nbits(current_target) == target_to_nbits(new_target))
    else:
        assert(current_target == prev_block_target)

def verify_timestamp(current_timestamp: int, prev_timestamps: list[int]):
    assert(len(prev_timestamps) == 11)
    median  = sorted(prev_timestamps)[5]
    assert(current_timestamp >= median)

def verify_current_header(hdr: bytes, validation_ctx: dict) -> dict:
    if validation_ctx["height_mod_2016"] != 0:
        assert(validation_ctx["prev_blockhash"] == hdr[4:36])
    validation_ctx["prev_blockhash"] = verify_pow(hdr)
    verify_target_update(
        hdr,
        validation_ctx["height_mod_2016"],
        validation_ctx["prev_block_target"],
        validation_ctx["prev_block_timestamp"],
        validation_ctx["epoch_start_timestamp"]
    )

    current_timestamp = parse_timestamp(hdr)
    verify_timestamp(current_timestamp, validation_ctx["prev_timestamps"])
               
    validation_ctx["prev_block_target"] = nbits_to_target(hdr[72:76])
    validation_ctx["prev_block_timestamp"] = current_timestamp
    validation_ctx["prev_timestamps"].insert(0, current_timestamp)
    validation_ctx["prev_timestamps"].pop()

    if validation_ctx["height_mod_2016"] == 2016:
        validation_ctx["epoch_start_timestamp"] = parse_timestamp(hdr)
        validation_ctx["height_mod_2016"] = 1
    else:
        validation_ctx["height_mod_2016"] += 1
    return validation_ctx

def verify_headers(filename, num_headers):
    # Block header validation context
    validation_ctx = {
        "height_mod_2016": 0,
        "prev_block_target": nbits_to_target(MAX_TARGET_BYTES),
        "prev_block_timestamp": 0,
        "epoch_start_timestamp": 1231006505,
        "prev_timestamps": [0]*11,
        "prev_blockhash": bytes(),
    }
    height = 0
    chain_work = 0

    with open(filename, 'r') as f:
        for line in f:
            if height < num_headers:
                hdr_hex = line.strip()
                hdr = bytes.fromhex(hdr_hex)
                assert(len(hdr) == 80)
                
                validation_ctx = verify_current_header(hdr, validation_ctx)
                chain_work += (2**256) // (nbits_to_target(hdr[72:76]) + 1)
                print("Block " + str(height) + " verified. Chainwork = " + str(hex(chain_work)))
                height = height+1

def main():
    parser = argparse.ArgumentParser(description="Verify BTC header chain")
    parser.add_argument("filename", help="Name of file with BTC headers (one per line as a hex string)")
    parser.add_argument("num_headers", type=int, help="Number of headers to verify")
    args = parser.parse_args()

    verify_headers(args.filename, args.num_headers)


if __name__ == "__main__":
    main()