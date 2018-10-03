module Benchmark = struct
    let time f = let start = Unix.gettimeofday () in
                 let result = Lazy.force f in
                 let stop = Unix.gettimeofday () in
                 (result, stop -. start)
end
