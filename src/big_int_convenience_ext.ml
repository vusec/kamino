include Big_int_convenience

let random bits = 
    let rounds = bits / (Nativeint.size) in
    let rec aux i acc = match i with
        | 0 -> 
                let bits_left = bits mod (Nativeint.size) in
                let bound = Nativeint.shift_left Nativeint.one bits_left in
                let random_bits = Random.nativeint bound in
                let widened_acc = Big_int_Z.shift_left_big_int acc bits_left in
                Big_int_Z.or_big_int widened_acc (Big_int_Z.big_int_of_nativeint random_bits)
        | _ -> 
            let bound = Nativeint.shift_left Nativeint.one Nativeint.size in
            let random_bits = Random.nativeint bound in
            let widened_acc = Big_int_Z.shift_left_big_int acc Nativeint.size in
            let new_acc = Big_int_Z.or_big_int widened_acc
            (Big_int_Z.big_int_of_nativeint random_bits) in
            aux (i-1) new_acc
    in
    aux rounds Big_int_Z.zero_big_int
