# Subnetfind

Ever been in this situation?

```console
$ docker-compose up
ERROR: could not find an available, non-overlapping IPv4 address pool among the
       defaults to assign to the network
```

**Subnetfind** is a tool (or a hack) that helps you to dynamically allocate
networks on your Linux system when.

This tool grew out of frustration over running Docker alongside with OpenVPN
on the same system.

## Status

This software is **experimental**.  Its interface and feature set are unstable
and I might take it down without further notice.

## License

This software is distributed under the terms of the 2-Clause BSD License.

See the [LICENSE](LICENSE) file in this repository for more information.
