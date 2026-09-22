let dir =
  let rec probe prefix n =
    let candidate = prefix ^ "tests/data" in
    if Sys.file_exists candidate then candidate
    else if n = 0 then failwith "tests/data not found from test cwd"
    else probe ("../" ^ prefix) (n - 1)
  in
  probe "" 5

let file name = Filename.concat dir name
